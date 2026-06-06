import BaseView from "app/client/components/BaseView";
import { GristDoc } from "app/client/components/GristDoc";
import { Delay } from "app/client/lib/Delay";
import { loadToastUICalendar, ToastUICalendarModule } from "app/client/lib/imports";
import { makeT } from "app/client/lib/localization";
import { ColumnRec, ViewSectionRec } from "app/client/models/DocModel";
import { reportError } from "app/client/models/errors";
import { basicButton, button, cssButtonGroup } from "app/client/ui2018/buttons";
import { theme } from "app/client/ui2018/cssVars";
import { icon } from "app/client/ui2018/icons";
import { gristThemeObs } from "app/client/ui2018/theme";
import { getReadableColorsCombo } from "app/client/widgets/ChoiceToken";
import { CellValue, UserAction } from "app/common/DocActions";
import { ColumnsToMap, WidgetColumnMap } from "app/plugin/CustomSectionAPI";
import { UIRowId } from "app/plugin/GristAPI";
import { decodeObject } from "app/plugin/objtypes";

import { Computed, dom, fromKo, IDisposable, makeTestId, Observable, styled } from "grainjs";
import debounce from "lodash/debounce";

import type Calendar from "@toast-ui/calendar";
import type { EventObject, Options, TZDate } from "@toast-ui/calendar";

// TUI's theme types live behind a non-exported DeepPartial<ThemeState>; pull them off Options so
// _calendarTheme is type-checked structurally (typos in deeply-nested keys become compile errors).
type CalendarThemeOption = NonNullable<Options["theme"]>;

const t = makeT("CalendarView");
const testId = makeTestId("test-calendar-");

// The single TUI "calendar" all events belong to.
const CALENDAR_NAME = "standardCalendar";

type Perspective = "day" | "week" | "month";
const PERSPECTIVES: Perspective[] = ["day", "week", "month"];

const SECONDS_PER_DAY = 24 * 60 * 60;

// Pointer travel (px) before a chip mousedown becomes a drag rather than a click.
const DRAG_THRESHOLD_PX = 4;

// Columns the calendar needs the user to map. Mirrors the mapping offered by the
// (now superseded) custom calendar widget, so existing configurations keep working.
// TODO(O6): the description strings here ("starting point of event", "is event all day long",
// "event category and style") read awkwardly; polish for a future i18n pass — e.g. "Start of the
// event", "Whether the event lasts all day", "Event category for color/style".
function getCalendarColumns(): ColumnsToMap {
  return [
    {
      name: "startDate",
      title: t("Start Date"),
      optional: false,
      type: "Date,DateTime",
      description: t("starting point of event"),
      allowMultiple: false,
      strictType: true,
    },
    {
      name: "endDate",
      title: t("End Date"),
      optional: true,
      type: "Date,DateTime",
      description: t("ending point of event"),
      allowMultiple: false,
      strictType: true,
    },
    {
      name: "isAllDay",
      title: t("Is All Day"),
      optional: true,
      type: "Bool",
      description: t("is event all day long"),
      strictType: true,
    },
    {
      name: "title",
      title: t("Title"),
      optional: false,
      type: "Text",
      description: t("title of event"),
      allowMultiple: false,
    },
    {
      name: "type",
      title: t("Type"),
      optional: true,
      type: "Choice,ChoiceList",
      description: t("event category and style"),
      allowMultiple: false,
    },
  ];
}

function isZeroTime(date: Date): boolean {
  return date.getHours() === 0 && date.getMinutes() === 0 && date.getSeconds() === 0;
}

// Date and DateTime are the only column types the calendar uses for start/end. We routinely need
// to discriminate between them (timezone handling, all-day inference); centralize that here so
// the checks read by intent. isDateLikeType in app/common/gristTypes is the "either of those"
// gate; these local helpers are the per-flavor specializations.
function isDateOnly(colType: string): boolean { return colType === "Date"; }
function isDateTime(colType: string): boolean { return colType.startsWith("DateTime"); }

// A row with a title but no start date, shown in the unassigned side panel.
interface UnassignedRecord {
  id: number;
  title: string;
}

// A flat record built from the mapped columns of a single row.
interface CalendarRecord {
  id: number;
  startDate: Date | null;
  endDate: Date | null;
  isAllDay: boolean | undefined;
  title: string | null;
  type: string;
}

/**
 * CalendarView renders records of the underlying table as events in a Toast UI Calendar, with
 * day/week/month perspectives. It is the native replacement for the bundled custom calendar
 * widget: same column mapping (start/end/title/all-day/type), same timezone and color handling,
 * but rendered directly (no iframe) and writing back through ordinary user actions.
 */
export class CalendarView extends BaseView {
  private _calendar: Calendar | null = null;
  private _tzDate: ToastUICalendarModule["TZDate"] | null = null;

  private _calendarDom: HTMLElement;
  private _titleDom: HTMLElement;

  // All events by Grist rowId; only those in the visible date range are pushed to TUI.
  private _allEvents = new Map<number, EventObject>();
  private _visibleEventIds = new Set<number>();
  private _selectedRecordId: number | null = null;

  // Set by the double-click-on-an-event handler to tell the popup observer to close the create
  // form popup TUI opens for that same double-click (we show the Record Card instead).
  private _suppressFormPopup = false;

  // Rows that have a title but no start date. They can't be placed on the grid, so we list
  // them in a side panel and let the user drag them onto a day to assign a date.
  private _unassigned = Observable.create<UnassignedRecord[]>(this, []);
  private _unassignedCollapsed = Observable.create(this, false);

  private _perspective: Computed<Perspective>;
  private _update: () => void;
  private _resize: () => void;

  constructor(gristDoc: GristDoc, viewSectionModel: ViewSectionRec) {
    super(gristDoc, viewSectionModel);

    // Derived from the saved option (defaulting to "week"); drives dom.cls in the toolbar and
    // _changeView via its listener. Persisted by _setPerspective. Must exist before _buildDom().
    this._perspective = Computed.create(this,
      fromKo(this.viewSection.optionsObj.prop("calendarViewPerspective")),
      (_use, view) => (view && PERSPECTIVES.includes(view) ? view : "week"));

    this.viewPane = this._buildDom();
    this.onDispose(() => {
      this._calendar?.destroy();
      dom.domDispose(this.viewPane);
      this.viewPane.remove();
    });

    // Advertise the columns we want mapped, so the creator panel shows the mapping UI (the same
    // path used by custom widgets). Clear on dispose so switching widget type doesn't leave a
    // stale mapping request behind.
    this.viewSection.columnsToMap(getCalendarColumns());
    // Opt this section in as a valid link source. LinkNode.ts only blocks link sources whose
    // widgetType is exactly "custom" (see app/common/LinkNode.ts), so a native "calendar" section
    // (or a legacy "custom.calendar" one, handled by the alias in ViewLayout.ts) isn't blocked
    // today. We still set the flag defensively, and reset it on dispose so a later switch to a
    // real custom widget doesn't inherit it.
    this.viewSection.allowSelectBy(true);
    this.onDispose(() => {
      if (this.viewSection.isDisposed()) { return; }
      this.viewSection.columnsToMap(null);
      this.viewSection.allowSelectBy(false);
    });

    this._update = debounce(() => this._updateView(), 0);
    this._resize = this.autoDispose(Delay.untilAnimationFrame(() => this._calendar?.render(), this));

    // Re-render events when data, mapping, perspective or theme change.
    this.listenTo(this.sortedRows, "rowNotify", this._update);
    this.autoDispose(this.sortedRows.getKoArray().subscribe(this._update));

    // Re-render when the mapping changes _or_ when one of the mapped columns' types changes
    // (Text -> Numeric, Date <-> DateTime, etc.). Mirrors ChartView's per-field type listener.
    let typeSubs: IDisposable[] = [];
    this.autoDispose(this.viewSection.mappedColumns.subscribe(() => {
      this._update();
      typeSubs.forEach(s => s.dispose());
      typeSubs = this._mappedColumnList().flatMap(col => [
        col.type.subscribe(this._update),
        col.displayColModel.peek().type.subscribe(this._update),
      ]);
    }));
    this.onDispose(() => typeSubs.forEach(s => s.dispose()));

    this.autoDispose(this._perspective.addListener(view => this._changeView(view)));
    // Event colors are set to CSS-variable strings, so they re-resolve on theme change with no
    // data rebuild; we only need to re-apply the calendar chrome theme.
    this.autoDispose(gristThemeObs().addListener(() => {
      this._calendar?.setTheme(this._calendarTheme());
    }));

    // Reflect the table cursor onto the calendar (selection + navigation).
    this.autoDispose(this.cursor.rowId.subscribe(rowId => this._selectRecord(rowId)));

    this._init().catch(reportError);

    // Stable handle for nbrowser tests, so they don't have to walk into private fields. Updated
    // to point at the most-recently-created live view, cleared on dispose. Production never
    // reads it; tests do via window.gristCalendarView (see test/nbrowser/CalendarView.ts).
    (window as any).gristCalendarView = this._testHook();
    this.onDispose(() => {
      if ((window as any).gristCalendarView?._view === this) {
        delete (window as any).gristCalendarView;
      }
    });
  }

  private _testHook() {
    return {
      _view: this,
      getEventByRowId: (rowId: number) => this._serializeEvent(this._allEvents.get(rowId)),
      getEventByTitle: (title: string) => this._serializeEvent(
        [...this._allEvents.values()].find(e => e.title === title)),
      getSelectedRecordId: () => this._selectedRecordId,
      getViewName: () => this._calendar?.getViewName(),
      getCalendarDate: () => this._calendar?.getDate().toDate().toDateString(),
      getUnassignedTitles: () => this._unassigned.get().map(r => r.title),
    };
  }

  private _serializeEvent(ev: EventObject | undefined) {
    if (!ev) { return null; }
    // TZDate carries a timezone tag; .local() recovers the original instant before .toDate().
    const ms = (x: any) => !x ? null : (x.toDate ? x.local().toDate().getTime() : new Date(x).getTime());
    return { title: ev.title, startMs: ms(ev.start), endMs: ms(ev.end), isAllDay: Boolean(ev.isAllday) };
  }

  public onResize() {
    this._resize();
  }

  protected onTableLoaded() {
    super.onTableLoaded();
    this._update();
  }

  // ---------------------------------------------------------------------------
  // Setup

  private async _init() {
    const { Calendar: CalendarCtor, TZDate } = await loadToastUICalendar();
    if (this.isDisposed()) { return; }
    this._tzDate = TZDate;

    const isReadOnly = this._isReadOnly();
    this._calendar = new CalendarCtor(this._calendarDom, {
      week: { taskView: false, startDayOfWeek: getFirstDayOfWeek() },
      month: { startDayOfWeek: getFirstDayOfWeek() },
      usageStatistics: false,   // never phone home to Google Analytics
      defaultView: this._perspective.get(),
      isReadOnly,
      theme: this._calendarTheme(),
      useFormPopup: !isReadOnly,
      useDetailPopup: false,    // we open Grist's Record Card on double-click instead
      // Double-click an empty cell to create an event (TUI opens its create form popup, positioned
      // at the click). Double-click an existing event opens Grist's Record Card instead; in that
      // case the create form popup would also open, mispositioned off to the side (its arrow point
      // is the average of the two click coordinates), so we suppress it (see _suppressFormPopup).
      gridSelection: { enableDblClick: true, enableClick: false },
      template: {
        // TUI's hour axis defaults to 12-hour ("3 pm") but its now-indicator label defaults to
        // 24-hour ("15:44"), so the two disagree. Format the now-indicator in the same 12-hour
        // style so the axis and the current-time marker read consistently.
        timegridNowIndicatorLabel: ({ time }) => formatHourMinute(time),
      },
      calendars: [{
        id: CALENDAR_NAME,
        name: t("Personal"),
        backgroundColor: theme.inputReadonlyBorder.toString(),
        borderColor: theme.inputReadonlyBorder.toString(),
      }],
    });

    this._wireCalendarEvents();
    // disableEditing is a ko.computed that depends on linking state (BaseView.ts), so it can flip
    // after init when the section becomes a link target. Mirror its current value onto TUI so the
    // form popup and drag-to-edit follow the read-only flag.
    this.autoDispose(this.disableEditing.subscribe(() => this._applyReadOnly()));
    // The TUI constructor already opened `defaultView` (this._perspective), so no _changeView here;
    // _updateView renders the events and title.
    this._updateView();
    // Apply the current cursor now that the calendar and its events exist: the cursor subscription
    // only fires on later changes, so an event the cursor already sits on (e.g. reopening a view
    // with a set cursor) wouldn't be highlighted until the cursor next moved.
    this._selectRecord(this.cursor.rowId.peek());
  }

  private _applyReadOnly() {
    if (!this._calendar) { return; }
    const isReadOnly = this._isReadOnly();
    this._calendar.setOptions({ isReadOnly, useFormPopup: !isReadOnly });
  }

  // TUI theme, expressed in terms of Grist theme CSS variables so it follows light/dark mode.
  private _calendarTheme(): CalendarThemeOption {
    const border = `1px solid ${theme.tableBodyBorder}`;
    const textColor = theme.text.toString();
    return {
      common: {
        backgroundColor: theme.mainPanelBg.toString(),
        border,
        holiday: { color: textColor },
        saturday: { color: textColor },
        dayName: { color: textColor },
        today: { color: textColor },
        gridSelection: {
          backgroundColor: theme.selection.toString(),
          border: `1px solid ${theme.selection}`,
        },
      },
      week: {
        dayName: { borderTop: border, borderBottom: border },
        timeGrid: { borderRight: border },
        timeGridLeft: { borderRight: border },
        dayGrid: { borderRight: border },
        dayGridLeft: { borderRight: border },
        timeGridHourLine: { borderBottom: border },
        nowIndicatorLabel: { color: theme.accentText.toString() },
        pastTime: { color: textColor },
        futureTime: { color: textColor },
        today: { color: textColor, backgroundColor: "inherit" },
      },
      month: {
        dayName: { borderLeft: border, backgroundColor: "inherit" },
        dayExceptThisMonth: { color: textColor },
        holidayExceptThisMonth: { color: textColor },
      },
    };
  }

  private _wireCalendarEvents() {
    const cal = this._calendar!;

    // A single click on an event selects its row (and drives grid linking). The handler parameter
    // types are inferred via TUI's ExternalEventTypes (see eventBus.d.ts), so we get EventObject etc.
    // for free with no explicit annotations.
    cal.on("clickEvent", ({ event }) => {
      const rowId = Number(event.id);
      if (!rowId || Number.isNaN(rowId)) { return; }
      this._selectRow(rowId);
    });

    // Double-click opens the Record Card. TUI doesn't emit a double-click event for an event item,
    // and a native double-click only produces a single TUI clickEvent, so we can't synthesize one
    // from two clickEvents. Instead we listen for the native DOM dblclick, which does reach the
    // grid, and resolve the event from the clicked element's data-event-id.
    this._calendarDom.addEventListener("dblclick", (ev) => {
      const eventEl = (ev.target as HTMLElement | null)?.closest("[data-event-id]");
      const rowId = eventEl && Number(eventEl.getAttribute("data-event-id"));
      if (!rowId || Number.isNaN(rowId)) { return; }
      // Double-click landed on an event, not an empty cell: open the Record Card and suppress the
      // create form popup that TUI will still open (mispositioned) for this same double-click.
      this._suppressFormPopup = true;
      this._selectRow(rowId);
      this.viewSelectedRecordAsCard();
    });

    // Creation, drag/resize and form edits.
    cal.on("beforeCreateEvent", (eventData) => this._upsertFromToast(null, eventData));
    cal.on("beforeUpdateEvent", ({ event, changes }) =>
      this._upsertFromToast(Number(event.id), changes));
    cal.on("beforeDeleteEvent", (event) => this._deleteEvent(Number(event.id)));

    // Clear leftover grid selections, mirroring the upstream workaround for nhn/tui.calendar#1300.
    this._calendarDom.addEventListener("mousedown", () => cal.clearGridSelections());
    // TODO(O4): the original custom widget worked around a TUI bug where a too-fast mouseup left
    // a stale drag (it called the v1-only `cancelDrag()`). TUI v2 doesn't expose an equivalent
    // public API; leaving as a known gap rather than risking a wrong fix. Resurrect via a
    // private-API call (and a comment) if QA hits the bug on touch devices.

    // Enter confirms the event-edit form popup (TUI doesn't submit it on Enter by itself).
    // Escape closes it without saving. Both reach into TUI's internal DOM via private class
    // names: `toastui-calendar-popup-confirm` and `toastui-calendar-popup-close`. There is no
    // public API exposing these buttons, and the popup is rendered into TUI's own container, so
    // there's no first-class way to wire keyboard handlers. If a TUI upgrade renames these
    // classes, the popup will silently stop responding to Enter/Escape; we'd find that via the
    // nbrowser tests, but worth being aware of when bumping the dependency.
    this._calendarDom.addEventListener("keydown", (ev) => {
      if (ev.key === "Enter") {
        const confirm = this._calendarDom.querySelector("button.toastui-calendar-popup-confirm");
        if (confirm) { ev.preventDefault(); (confirm as HTMLElement).click(); }
      } else if (ev.key === "Escape") {
        const close = this._calendarDom.querySelector("button.toastui-calendar-popup-close");
        if (close) { ev.preventDefault(); (close as HTMLElement).click(); }
      }
    });

    // When the form popup opens, autofocus the title input so users can type immediately.
    // TUI doesn't expose a "popup opened" event, so we observe DOM mutations on the calendar
    // container and react to the popup container appearing. We only focus on the closed->open
    // transition: focusing on every mutation would steal focus back to the title whenever the
    // user clicked into another field (date, location) of an already-open popup. The title field
    // is `input[name="title"]` inside the popup container (TUI's internal markup, like the
    // popup-button handling above; verified against the rendered DOM).
    let popupWasOpen = false;
    const observer = new MutationObserver(() => {
      const popup = this._calendarDom.querySelector(".toastui-calendar-popup-container");
      const popupIsOpen = Boolean(popup);
      if (popupIsOpen && !popupWasOpen) {
        // A double-click on an event opens the Record Card, but TUI still opens its create form
        // popup for that same double-click, mispositioned. Close it as soon as it appears.
        if (this._suppressFormPopup) {
          this._suppressFormPopup = false;
          const close = popup!.querySelector("button.toastui-calendar-popup-close") as HTMLElement | null;
          close?.click();
          this._calendar?.clearGridSelections();
        } else {
          const titleInput = popup!.querySelector("input[name='title']") as HTMLInputElement | null;
          titleInput?.focus();
        }
      }
      popupWasOpen = popupIsOpen;
    });
    observer.observe(this._calendarDom, { childList: true, subtree: true });
    this.onDispose(() => observer.disconnect());
  }

  // ---------------------------------------------------------------------------
  // Column mapping

  private _mapping(): WidgetColumnMap {
    return this.viewSection.mappedColumns() || {};
  }

  private _col(value: string | string[] | null | undefined): ColumnRec | null {
    const colId = Array.isArray(value) ? value[0] : value;
    if (!colId) { return null; }
    return this.viewSection.columns.peek().find(c => c.colId.peek() === colId) || null;
  }

  // The column whose value should be read for display. For a Reference column this resolves to
  // the visible column on the referenced table; for plain columns it returns the column itself.
  // Mirrors ChartView's use of `displayColModel` (see ChartView.ts) so we behave consistently.
  private _displayCol(col: ColumnRec | null): ColumnRec | null {
    return col ? col.displayColModel.peek() : null;
  }

  // All ColumnRecs currently referenced by the calendar's mapping (deduplicated). Used to wire
  // type-change subscriptions, since the calendar's rendering depends on each column's pureType.
  private _mappedColumnList(): ColumnRec[] {
    const mapping = this._mapping();
    const cols = ["startDate", "endDate", "isAllDay", "title", "type"]
      .map(key => this._col(mapping[key]))
      .filter((c): c is ColumnRec => c !== null);
    return Array.from(new Set(cols));
  }

  // ---------------------------------------------------------------------------
  // Reading data

  private _updateView() {
    if (this.isDisposed() || !this._calendar) { return; }

    const mapping = this._mapping();
    const startCol = this._col(mapping.startDate);
    const titleCol = this._col(mapping.title);
    // Both required columns must be mapped to show anything.
    if (!startCol || !titleCol) {
      this._allEvents = new Map();
      this._setUnassigned([]);
      this._renderVisibleEvents();
      this._updateTitle();
      return;
    }
    const endCol = this._col(mapping.endDate);
    const allDayCol = this._col(mapping.isAllDay);
    const typeCol = this._col(mapping.type);

    // Read values via the display column so that Reference columns surface their visible value
    // (e.g. an event title) instead of the foreign row id. For non-Ref columns this is a no-op.
    const startDisplay = this._displayCol(startCol)!;
    const endDisplay = this._displayCol(endCol);
    const titleDisplay = this._displayCol(titleCol)!;
    const allDayDisplay = this._displayCol(allDayCol);
    const typeDisplay = this._displayCol(typeCol);

    // Resolve column types, choice styling and the doc timezone once, not per row.
    const startType = startDisplay.pureType.peek();
    const endType = endDisplay?.pureType.peek() || startType;
    const choiceOptions = typeDisplay?.widgetOptionsJson.peek()?.choiceOptions || {};
    const docTz = this._docTimeZone();

    // Build one getter per mapped column; per-row access is then a plain array read
    // rather than a getValue() map lookup (same approach as ChartView).
    const data = this.tableModel.tableData;
    const getStart = data.getRowPropFunc(startDisplay.colId.peek());
    const getTitle = data.getRowPropFunc(titleDisplay.colId.peek());
    const getEnd = endDisplay && data.getRowPropFunc(endDisplay.colId.peek());
    const getAllDay = allDayDisplay && data.getRowPropFunc(allDayDisplay.colId.peek());
    const getType = typeDisplay && data.getRowPropFunc(typeDisplay.colId.peek());

    const rowIds = this.sortedRows.getKoArray().peek() as number[];
    const events: [number, EventObject][] = [];
    const unassigned: UnassignedRecord[] = [];
    for (const rowId of rowIds) {
      if (typeof rowId !== "number") { continue; }
      const startDate = numToDate(getStart(rowId));
      const title = asText(getTitle(rowId));
      // A row with no title can't be shown anywhere; skip it. A titled row with no start date
      // can't be placed on the grid, so it goes to the unassigned panel instead of being lost.
      if (title === null) { continue; }
      if (!startDate) { unassigned.push({ id: rowId, title }); continue; }
      const record: CalendarRecord = {
        id: rowId,
        startDate,
        endDate: getEnd ? numToDate(getEnd(rowId)) : null,
        isAllDay: getAllDay ? Boolean(getAllDay(rowId)) : undefined,
        title,
        type: getType ? asChoice(getType(rowId)) : "",
      };
      events.push([rowId, this._buildEvent(record, startType, endType, choiceOptions, docTz)]);
    }

    this._allEvents = new Map(events);
    this._setUnassigned(unassigned);
    this._renderVisibleEvents();
    this._updateTitle();
    this._refreshSelectedRecord();
  }

  // _updateView runs on every data/mapping/perspective/theme change, but the unassigned list rarely
  // changes; only notify the panel's bindings when the ids/titles actually differ.
  private _setUnassigned(next: UnassignedRecord[]) {
    const prev = this._unassigned.get();
    if (prev.length === next.length &&
        prev.every((r, i) => r.id === next[i].id && r.title === next[i].title)) {
      return;
    }
    this._unassigned.set(next);
  }

  private _buildEvent(
    record: CalendarRecord, startType: string, endType: string, choiceOptions: Record<string, any>,
    docTz: string,
  ): EventObject {
    const start = this._getAdjustedDate(record.startDate!, startType, docTz);
    let end = record.endDate ? this._getAdjustedDate(record.endDate, endType, docTz) : start;

    // Normalize invalid ranges so the event is still visible.
    if (end < start) { end = start; }

    let isAllday = record.isAllDay;
    if (isDateOnly(startType) && isDateOnly(endType)) { isAllday = true; }
    // Workaround for midnight zero-length events not showing up.
    if (!isAllday && end.valueOf() === start.valueOf() && isZeroTime(end) && isZeroTime(start)) {
      end = new this._tzDate!(end).addHours(1) as unknown as Date;
    }

    // Apply colors/styling from the choice options of the "type" column, falling back to defaults.
    // getReadableColorsCombo picks a readable text shade when a choice has a custom fill but no
    // custom text color, so events with a dark fill don't render near-invisible text.
    const style = choiceOptions[record.type] || {};
    const { bg: backgroundColor, fg: color } = getReadableColorsCombo(
      { fillColor: style.fillColor, textColor: style.textColor },
      { bg: theme.inputReadonlyBorder.toString(), fg: theme.text.toString() },
    );
    const fontWeight = style.fontBold ? "800" : "normal";
    const fontStyle = style.fontItalic ? "italic" : "normal";
    let textDecoration = style.fontUnderline ? "underline" : "none";
    if (style.fontStrikethrough) {
      textDecoration = textDecoration === "underline" ? "line-through underline" : "line-through";
    }

    return {
      id: String(record.id),
      calendarId: CALENDAR_NAME,
      title: record.title!,
      start,
      end,
      isAllday,
      category: isAllday ? "allday" : "time",
      // TUI's EventState is "Busy" | "Free"; we treat all Grist rows as Free since we don't
      // track availability semantics. Typed via EventObject["state"] rather than a bare literal
      // so a TUI rename surfaces at compile time.
      state: "Free" satisfies NonNullable<EventObject["state"]>,
      backgroundColor,
      color,
      borderColor: backgroundColor,
      dragBackgroundColor: theme.hover.toString(),
      // Remember the base background so _setHighlight can restore it after a selection.
      raw: { backgroundColor },
      customStyle: { fontStyle, fontWeight, textDecoration, textWrap: "auto" },
    } as EventObject;
  }

  // ---------------------------------------------------------------------------
  // Timezone handling (ported from the calendar widget)

  private _docTimeZone(): string {
    return this.gristDoc.docInfo.timezone.peek();
  }

  /** Shifts a UTC-based JS Date so it displays correctly for the given column type. */
  private _getAdjustedDate(date: Date, colType: string, docTz: string): Date {
    // The `timezone` property exists on TZDate (TUI's wrapper) but not on plain Date — we still
    // call this with both, so probe the field rather than narrowing the parameter type.
    const dateTz = (date as Date & { timezone?: string }).timezone;
    if (docTz && docTz !== dateTz && isDateTime(colType)) {
      return new this._tzDate!(date).tz(docTz) as unknown as Date;
    }
    if (!isDateOnly(colType)) { return date; }
    // Like date.tz('UTC'), but accounts for DST differences.
    const ms = date.valueOf() + (date.getTimezoneOffset() * 60000);
    return new Date(ms);
  }

  /** Converts a calendar date (browser-local TZDate) into the seconds value Grist stores. */
  private _makeGristDateTime(tzDate: TZDate, colType: string): number {
    let unixTime = Math.floor(tzDate.valueOf() / 1000);
    const localOffsetMin = -tzDate.getTimezoneOffset();
    const docTz = this._docTimeZone();
    const docOffsetMin = !docTz ? localOffsetMin : tzDate.tz(docTz).getTimezoneOffset();
    if (isDateOnly(colType)) {
      const secondsSinceEpoch = unixTime + localOffsetMin * 60;
      return Math.floor(secondsSinceEpoch / SECONDS_PER_DAY) * SECONDS_PER_DAY;
    } else {
      unixTime += (localOffsetMin - docOffsetMin) * 60;
      return unixTime;
    }
  }

  // ---------------------------------------------------------------------------
  // Writing data

  private async _upsertFromToast(rowId: number | null, tui: Partial<EventObject>) {
    if (this._isReadOnly()) { return; }
    const mapping = this._mapping();
    const startCol = this._col(mapping.startDate);
    const endCol = this._col(mapping.endDate);
    const allDayCol = this._col(mapping.isAllDay);
    const titleCol = this._col(mapping.title);

    const fields: Record<string, CellValue> = {};
    if (tui.start !== undefined && startCol) {
      fields[startCol.colId.peek()] = this._makeGristDateTime(tui.start as TZDate, startCol.pureType.peek());
    }
    if (tui.end !== undefined && endCol) {
      fields[endCol.colId.peek()] = this._makeGristDateTime(tui.end as TZDate, endCol.pureType.peek());
    }
    if (tui.isAllday !== undefined && allDayCol) {
      fields[allDayCol.colId.peek()] = tui.isAllday;
    }
    if (tui.title !== undefined && titleCol) {
      fields[titleCol.colId.peek()] = tui.title || t("New Event");
    }
    if (Object.keys(fields).length === 0) { return; }

    try {
      if (rowId) {
        await this.sendTableAction(["UpdateRecord", rowId, fields] as UserAction);
      } else {
        const newRowId = await this.sendTableAction(["AddRecord", null, fields] as UserAction);
        // setCursorPos triggers _selectRecord on a rowId whose event isn't in _allEvents yet
        // (rowNotify fires asynchronously). _selectedRecordId acts as a pending pointer; the next
        // _updateView (via rowNotify) reconciles the highlight through _refreshSelectedRecord.
        if (newRowId && !this.isDisposed()) { this.setCursorPos({ rowId: newRowId }); }
      }
    } catch (err) {
      reportError(err as Error);
    }
  }

  private async _deleteEvent(rowId: number) {
    if (this._isReadOnly() || !rowId) { return; }
    try {
      await this.deleteRows([rowId]);
    } catch (err) {
      reportError(err as Error);
    }
  }

  // Move the grid cursor (and active section) to a row. Shared by event clicks and the
  // unassigned panel so both light up the linked row the same way.
  private _selectRow(rowId: number) {
    this.gristDoc.viewModel.activeSectionId(this.viewSection.getRowId());
    this.setCursorPos({ rowId });
  }

  // Press-and-drag a chip from the unassigned panel onto the grid. We track the pointer on the
  // document and, on release over the calendar grid, map the drop point to a date and assign it.
  // A release that didn't move (below DRAG_THRESHOLD_PX) is left to the chip's click handler.
  private _startChipDrag(downEv: MouseEvent, rowId: number) {
    if (downEv.button !== 0 || this._isReadOnly()) { return; }
    const startX = downEv.clientX, startY = downEv.clientY;
    let dragging = false;
    const onMove = (ev: MouseEvent) => {
      if (!dragging && Math.hypot(ev.clientX - startX, ev.clientY - startY) > DRAG_THRESHOLD_PX) {
        dragging = true;
        document.body.classList.add(cssDraggingBody.className);
      }
    };
    const onUp = (ev: MouseEvent) => {
      document.removeEventListener("mousemove", onMove);
      document.removeEventListener("mouseup", onUp);
      document.body.classList.remove(cssDraggingBody.className);
      if (!dragging) { return; }   // treat as a click, handled separately
      const rect = this._calendarDom.getBoundingClientRect();
      const over = ev.clientX >= rect.left && ev.clientX <= rect.right &&
        ev.clientY >= rect.top && ev.clientY <= rect.bottom;
      if (!over) { return; }
      const date = this._dateAtPoint(ev.clientX, ev.clientY);
      if (date) { this._assignDate(rowId, date).catch(reportError); }
    };
    document.addEventListener("mousemove", onMove);
    document.addEventListener("mouseup", onUp);
  }

  // Writes a start date to a previously-unassigned row, so it moves onto the grid. Reuses the
  // same date conversion and update path as drag/resize (_upsertFromToast).
  private async _assignDate(rowId: number, date: Date) {
    if (this._isReadOnly() || !this._tzDate) { return; }
    const startCol = this._col(this._mapping().startDate);
    if (!startCol) { return; }
    const tzDate = new this._tzDate(date) as unknown as TZDate;
    const fields: Record<string, CellValue> = {
      [startCol.colId.peek()]: this._makeGristDateTime(tzDate, startCol.pureType.peek()),
    };
    try {
      await this.sendTableAction(["UpdateRecord", rowId, fields] as UserAction);
      if (!this.isDisposed()) { this.setCursorPos({ rowId }); }
    } catch (err) {
      reportError(err as Error);
    }
  }

  // Maps a drop point inside the calendar grid to a date. TUI exposes no x/y -> date API and its
  // cells carry no date attribute, so we hit-test its rendered grid elements: TUI lays them out in
  // day order starting at getDateRangeStart(), so a cell's index is its offset in days. Hit-testing
  // the real elements (rather than slicing the container by fractions) automatically skips the week
  // view's left hour-gutter and the month view's day-name header, and survives uneven cell sizes.
  // The time of day is left at midnight; the user fine-tunes by dragging the resulting event.
  // Returns null if the point isn't over the grid.
  private _dateAtPoint(clientX: number, clientY: number): Date | null {
    const cal = this._calendar;
    if (!cal) { return null; }
    const view = cal.getViewName();
    if (view === "day") {
      return atMidnight(cal.getDate().toDate());
    }
    const rangeStart = atMidnight(cal.getDateRangeStart().toDate());
    // week: 7 day-columns rendered left-to-right inside the columns wrapper (the hour-gutter sits
    // outside it). The column under the pointer's x gives the day offset.
    if (view === "week") {
      const columns = this._calendarDom.querySelectorAll(".toastui-calendar-column");
      const offset = indexOfElementAtX(columns, clientX);
      return offset === null ? null : addDays(rangeStart, offset);
    }
    // month: one day-cell per day, in row-major order from rangeStart. The cell containing the
    // pointer gives the day offset directly (no row/col arithmetic).
    const cells = this._calendarDom.querySelectorAll(".toastui-calendar-daygrid-cell");
    const offset = indexOfElementAtPoint(cells, clientX, clientY);
    return offset === null ? null : addDays(rangeStart, offset);
  }

  // ---------------------------------------------------------------------------
  // Selection / cursor linking

  private _selectRecord(rowId: UIRowId | null) {
    if (!this._calendar) { return; }
    const next = typeof rowId === "number" ? rowId : null;
    if (next === this._selectedRecordId) { return; }

    // Always clear the previous highlight, even when there's no incoming event to highlight
    // (e.g. cursor moved off any mapped row, or to a row whose date columns are blank).
    if (this._selectedRecordId) { this._setHighlight(this._selectedRecordId, false); }
    this._selectedRecordId = next;
    if (next === null) { return; }

    const event = this._allEvents.get(next);
    if (!event) { return; }

    this._calendar.setDate(event.start as TZDate);
    this._updateUIAfterNavigation();
  }

  private _refreshSelectedRecord() {
    if (this._selectedRecordId) { this._setHighlight(this._selectedRecordId, true); }
  }

  // Highlights (or un-highlights) an event by resetting it to its base color and, when selected,
  // overriding the border (or background, for month-view bars) with the accent color.
  private _setHighlight(rowId: number, selected: boolean) {
    const cal = this._calendar;
    const event = cal?.getEvent(String(rowId), CALENDAR_NAME);
    if (!cal || !event) { return; }
    const base = event.raw?.backgroundColor ?? theme.inputReadonlyBorder.toString();
    const part = this._isBarInMonthView(event) ? "backgroundColor" : "borderColor";
    cal.updateEvent(String(rowId), CALENDAR_NAME, {
      borderColor: base,
      backgroundColor: base,
      ...(selected ? { [part]: theme.controlPrimaryBg.toString() } : {}),
    });
  }

  private _isBarInMonthView(event: EventObject): boolean {
    if (this._calendar?.getViewName() !== "month") { return false; }
    const start = (event.start as TZDate).toDate();
    const end = (event.end as TZDate).toDate();
    const isMultiDay = start.getDate() !== end.getDate() ||
      start.getMonth() !== end.getMonth() ||
      start.getFullYear() !== end.getFullYear();
    return !isMultiDay;
  }

  // ---------------------------------------------------------------------------
  // Navigation & rendering

  /** Adds/updates events in the visible range and removes those that scrolled out of it. */
  private _renderVisibleEvents() {
    const cal = this._calendar;
    if (!cal) { return; }
    const rangeStart = cal.getDateRangeStart().getTime();
    // Copy before calling setHours, which mutates in place. TUI may hand back a reference to its
    // internal range-end, so shifting it would creep the visible window forward each render.
    const rangeEndDate = (cal.getDateRangeEnd() as TZDate).toDate();
    rangeEndDate.setHours(23, 59, 59, 999);
    const rangeEnd = rangeEndDate.getTime();

    const nowVisible = new Set<number>();
    for (const [rowId, event] of this._allEvents) {
      const startMs = (event.start as TZDate).getTime();
      const endMs = (event.end as TZDate).getTime();
      const inRange = (startMs >= rangeStart && startMs <= rangeEnd) ||
        (endMs >= rangeStart && endMs <= rangeEnd) ||
        (startMs < rangeStart && endMs > rangeEnd);
      if (!inRange) { continue; }
      if (cal.getEvent(String(rowId), CALENDAR_NAME)) {
        cal.updateEvent(String(rowId), CALENDAR_NAME, event);
      } else {
        cal.createEvents([event]);
      }
      nowVisible.add(rowId);
    }
    for (const rowId of this._visibleEventIds) {
      if (!nowVisible.has(rowId)) { cal.deleteEvent(String(rowId), CALENDAR_NAME); }
    }
    this._visibleEventIds = nowVisible;
  }

  private _changeView(view: Perspective) {
    this._calendar?.changeView(view);
    this._updateUIAfterNavigation();
  }

  private _go(method: "prev" | "next" | "today") {
    this._calendar?.[method]();
    this._updateUIAfterNavigation();
  }

  private _setPerspective(view: Perspective) {
    // Persist the choice; this flows back through _perspective (toolbar active state) and its
    // listener (_changeView), since setAndSave updates the underlying option synchronously.
    this.viewSection.optionsObj.prop("calendarViewPerspective").setAndSave(view).catch(reportError);
  }

  private _updateUIAfterNavigation() {
    this._renderVisibleEvents();
    this._updateTitle();
    this._refreshSelectedRecord();
  }

  private _updateTitle() {
    if (!this._calendar || !this._titleDom) { return; }
    this._titleDom.textContent = this._formatTitle();
  }

  // Title shown in the toolbar above the calendar grid.
  // - day view: a full date (e.g. "Wed, 9 Aug 2023").
  // - week view: the visible date range (e.g. "6 - 12 Aug 2023", or "30 Jul - 5 Aug 2023" when
  //   the week straddles a month boundary).
  // - month view: month + year.
  // TUI doesn't expose its own header text, but it does expose getDate / getDateRange* which give
  // us enough to derive these formats consistently.
  private _formatTitle(): string {
    const cal = this._calendar!;
    const view = cal.getViewName();
    const current = cal.getDate().toDate();
    if (view === "day") {
      return current.toLocaleDateString(undefined, {
        weekday: "short", day: "numeric", month: "short", year: "numeric",
      });
    }
    if (view === "week") {
      const start = cal.getDateRangeStart().toDate();
      const end = cal.getDateRangeEnd().toDate();
      const sameYear = start.getFullYear() === end.getFullYear();
      const sameMonth = sameYear && start.getMonth() === end.getMonth();
      const startFmt: Intl.DateTimeFormatOptions = sameMonth
        ? { day: "numeric" }
        : (sameYear ? { day: "numeric", month: "short" } : { day: "numeric", month: "short", year: "numeric" });
      const endFmt: Intl.DateTimeFormatOptions = { day: "numeric", month: "short", year: "numeric" };
      return `${start.toLocaleDateString(undefined, startFmt)} – ${end.toLocaleDateString(undefined, endFmt)}`;
    }
    return current.toLocaleDateString(undefined, { month: "long", year: "numeric" });
  }

  // ---------------------------------------------------------------------------
  // DOM

  private _isReadOnly(): boolean {
    return this.gristDoc.isReadonly.get() || this.disableEditing.peek();
  }

  private _buildDom() {
    // Build all field-bound nodes into locals first, then compose — easier to grep for the
    // _titleDom / _calendarDom assignments than spotting them inline in a tree literal.
    this._titleDom = cssCalendarTitle(testId("title"));
    this._calendarDom = cssCalendarContainer(testId("widget"));
    const navGroup = cssNavGroup(
      basicButton(icon("ArrowLeft"),
        dom.on("click", () => this._go("prev")), testId("prev")),
      basicButton(t("Today"), dom.on("click", () => this._go("today")), testId("today")),
      basicButton(icon("ArrowRight"),
        dom.on("click", () => this._go("next")), testId("next")),
    );
    // Day/Week/Month is a segmented toggle: the standard Grist button group, with the current view
    // shown as a primary button (so it uses the same active/hover colors as every other control).
    const perspectiveGroup = cssPerspectiveGroup(
      ...PERSPECTIVES.map(view =>
        button(
          { primary: use => use(this._perspective) === view },
          perspectiveLabel(view),
          dom.on("click", () => this._setPerspective(view)),
          testId(`perspective-${view}`),
        ),
      ),
    );
    return cssCalendarView(
      testId("container"),
      cssToolbar(navGroup, this._titleDom, perspectiveGroup),
      cssCalendarBody(
        this._calendarDom,
        this._buildUnassignedPanel(),
      ),
    );
  }

  // Side panel listing rows that have a title but no start date. Hidden entirely when there
  // are none, so it doesn't steal grid width in the common case. Each chip can be clicked (to
  // select its row) or dragged onto the grid (to assign a date, via the _calendarDom drop
  // handler in _wireCalendarEvents).
  private _buildUnassignedPanel() {
    return dom.maybe(use => use(this._unassigned).length > 0, () =>
      cssUnassignedPanel(
        cssUnassignedPanel.cls("-collapsed", this._unassignedCollapsed),
        testId("unassigned"),
        cssUnassignedHeader(
          dom.domComputed(this._unassignedCollapsed, (collapsed) =>
            icon(collapsed ? "Expand" : "Collapse")),
          dom("span", dom.text(use => t("Unassigned ({{count}})", { count: use(this._unassigned).length }))),
          dom.on("click", () => {
            this._unassignedCollapsed.set(!this._unassignedCollapsed.get());
            this.onResize();
          }),
          testId("unassigned-toggle"),
        ),
        dom.maybe(use => !use(this._unassignedCollapsed), () =>
          cssUnassignedList(
            dom.forEach(this._unassigned, (rec) =>
              cssUnassignedChip(
                rec.title || t("New Event"),
                // Plain click selects the row; press-and-drag onto the grid assigns a date.
                // We use manual pointer events (not HTML5 drag) so the gesture matches TUI's own
                // mouse-based dragging and stays drivable by the nbrowser tests.
                dom.on("mousedown", (ev) => this._startChipDrag(ev, rec.id)),
                dom.on("click", () => this._selectRow(rec.id)),
                testId("unassigned-chip"),
              ),
            ),
          ),
        ),
      ),
    );
  }
}

// ---------------------------------------------------------------------------
// Helpers

function numToDate(value: CellValue | undefined): Date | null {
  // 0 is how Grist stores a blank Date/DateTime; treat it as missing rather than 1970-01-01.
  // Matches ChartView's dateGetter, which excludes zero for the same reason.
  return (typeof value === "number" && value && isFinite(value)) ? new Date(value * 1000) : null;
}

function asText(value: CellValue | undefined): string | null {
  if (value === null || value === undefined || value === "") { return null; }
  return typeof value === "string" ? value : String(value);
}

function asChoice(value: CellValue | undefined): string {
  if (!value) { return ""; }
  const decoded = decodeObject(value);
  return String(Array.isArray(decoded) ? (decoded[0] ?? "") : decoded);
}

function atMidnight(date: Date): Date {
  const out = new Date(date);
  out.setHours(0, 0, 0, 0);
  return out;
}

// Index of the element whose horizontal span contains clientX (elements assumed left-to-right).
// Returns null if the point is left of the first or right of the last element.
function indexOfElementAtX(els: NodeListOf<Element>, clientX: number): number | null {
  for (let i = 0; i < els.length; i++) {
    const rect = els[i].getBoundingClientRect();
    if (clientX >= rect.left && clientX <= rect.right) { return i; }
  }
  return null;
}

// Index of the element whose box contains (clientX, clientY). Returns null if none does.
function indexOfElementAtPoint(els: NodeListOf<Element>, clientX: number, clientY: number): number | null {
  for (let i = 0; i < els.length; i++) {
    const rect = els[i].getBoundingClientRect();
    if (clientX >= rect.left && clientX <= rect.right &&
        clientY >= rect.top && clientY <= rect.bottom) { return i; }
  }
  return null;
}

function addDays(date: Date, days: number): Date {
  const out = new Date(date);
  out.setDate(out.getDate() + days);
  return out;
}

// Localized label for a perspective toolbar button. A switch with literal t(...) keys (rather than
// t(capitalize(view))) so the i18n string extractor can find "Day"/"Week"/"Month".
function perspectiveLabel(view: Perspective): string {
  switch (view) {
    case "day": return t("Day");
    case "week": return t("Week");
    case "month": return t("Month");
  }
}

// 12-hour "h:mm am/pm" for the now-indicator label, matching TUI's 12-hour hour axis. The argument
// is a TUI TZDate, which exposes getHours()/getMinutes() like a Date (the same accessors TUI's own
// format tokens use), so reading local wall-clock time here is correct.
function formatHourMinute(time: { getHours(): number; getMinutes(): number }): string {
  const hours = time.getHours();
  const minutes = time.getMinutes();
  const period = hours < 12 ? "am" : "pm";
  const hour12 = hours % 12 || 12;
  return `${hour12}:${String(minutes).padStart(2, "0")} ${period}`;
}

// TUI: 0=Sun..6=Sat; Intl: 1=Mon..7=Sun.
// Note: the original custom calendar widget honored a `?culture=<locale>` URL parameter as a
// locale override; the native view only reads navigator.language. If an admin deployment ever
// relied on `?culture=` to influence week start, that path no longer works here.
function getFirstDayOfWeek(): number {
  try {
    const locale = new Intl.Locale(navigator.language || "en");
    const weekInfo = (locale as any).getWeekInfo?.() ?? (locale as any).weekInfo;
    if (weekInfo?.firstDay !== undefined) {
      return weekInfo.firstDay === 7 ? 0 : weekInfo.firstDay;
    }
  } catch (e) {
    // Intl.Locale week info not supported by this browser.
  }
  return 0;
}

// ---------------------------------------------------------------------------
// Styles

const cssCalendarView = styled("div", `
  display: flex;
  flex-direction: column;
  height: 100%;
  width: 100%;
  background-color: ${theme.mainPanelBg};
  color: ${theme.text};
`);

const cssToolbar = styled("div", `
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 8px 16px;
  border-bottom: 1px solid ${theme.tableBodyBorder};
  flex: none;
`);

const cssNavGroup = styled("div", `
  display: flex;
  align-items: center;
  gap: 4px;
`);

const cssPerspectiveGroup = styled(cssButtonGroup, `
  align-items: center;
  margin-left: auto;
`);

const cssCalendarTitle = styled("div", `
  font-weight: 600;
  font-size: 15px;
  min-width: 160px;
  text-align: center;
`);

// Horizontal row holding the calendar grid and (optionally) the unassigned side panel.
const cssCalendarBody = styled("div", `
  display: flex;
  flex: 1 1 0;
  min-height: 0;
`);

const cssCalendarContainer = styled("div", `
  flex: 1 1 0;
  min-height: 0;
  min-width: 0;
  overflow: hidden;
  & .toastui-calendar-day-names.toastui-calendar-month {
    padding-left: 0;
    padding-right: 0;
  }
  & .toastui-calendar-weekday-grid-date-decorator {
    background-color: ${theme.controlPrimaryBg};
    color: ${theme.controlPrimaryFg};
  }
`);

const cssUnassignedPanel = styled("div", `
  flex: none;
  width: 200px;
  display: flex;
  flex-direction: column;
  border-left: 1px solid ${theme.tableBodyBorder};
  overflow: hidden;
  &-collapsed {
    width: auto;
  }
`);

const cssUnassignedHeader = styled("div", `
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 12px;
  font-weight: 600;
  cursor: pointer;
  user-select: none;
  --icon-color: ${theme.controlSecondaryFg};
  &:hover {
    background-color: ${theme.hover};
  }
`);

const cssUnassignedList = styled("div", `
  display: flex;
  flex-direction: column;
  gap: 4px;
  padding: 4px 8px 8px 8px;
  overflow-y: auto;
`);

const cssUnassignedChip = styled("div", `
  padding: 4px 8px;
  border-radius: 3px;
  background-color: ${theme.inputReadonlyBorder};
  color: ${theme.text};
  cursor: grab;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  user-select: none;
  &:hover {
    filter: brightness(0.95);
  }
`);

// Applied to <body> while a chip is being dragged, so the grab cursor persists over the grid.
const cssDraggingBody = styled("div", `
  cursor: grabbing !important;
`);
