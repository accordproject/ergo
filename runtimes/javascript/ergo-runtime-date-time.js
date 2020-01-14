/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* Addendum to the Ergo runtime for DateTime, Duration and Periods support */

/* Utilities */
var SECONDS = "second";
var MINUTES = "minute";
var HOURS = "hour";
var DAYS = "day";
var WEEKS = "week";
var MONTHS = "month";
var QUARTERS = "quarter";
var YEARS = "year";

function mustBeDate(date) {
    if (typeof date == "string") {
        return moment.parseZone(date).utcOffset(utcOffset, false);
    } else if (date instanceof Date) {
        return moment(date).utcOffset(utcOffset, false);
    } else {
        return date.clone().utcOffset(utcOffset, false);;
    }
}

function mustBeDateArray(dateArray) {
    var newDateArray = [];
    for (var i=0; i<dateArray.length; i++) {
        newDateArray.push(mustBeDate(dateArray[i]));
    }
    return newDateArray;
}

function mustBeDuration(d) {
    if (typeof d == "string") {
        return moment.duration(d);
    } else {
        return d.clone();
    }
}

function mustBeUnit(unit) {
    if (unit === SECONDS
        || unit === MINUTES
        || unit === HOURS
        || unit === DAYS
        || unit === WEEKS
        || unit === MONTHS
        || unit === QUARTERS
        || unit === YEARS)
	      return;
    throw new Error("Expected a duration unit but got " + JSON.stringify(unit));
}

function compareDates(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    if (date1.isBefore(date2)) {
        return -1;
    } else if (date1.isAfter(date2)) {
        return 1;
    } else if (date1.isSame(date2)) {
        return 0;
    }
    throw new Error("Unexpected failure: compareDates")
}

/* DateTime */
function dateTimeComponent(part, date) {
    date = mustBeDate(date);
    switch(part) {
    case SECONDS:
        return natBox(date.second());
    case MINUTES:
        return natBox(date.minute());
    case HOURS:
        return natBox(date.hour());
    case DAYS:
        return natBox(date.date());
    case WEEKS:
        return natBox(date.week());
    case MONTHS:
        return natBox(date.month() + 1); // Shift by one to get 1-12 range on months (Moment uses 0-11)
    case QUARTERS:
        return natBox(date.quarter());
    case YEARS:
        return natBox(date.year());
    default:
        throw new Error("Unknown DateTime component: " + part);
    }
}

function dateTimeFromString(stringDate) {
    return moment.parseZone(stringDate).utcOffset(utcOffset, false);
}

var minDateTime = moment.parseZone("0001-01-01 00:00:00").utcOffset(utcOffset, false);
var maxDateTime = moment.parseZone("3268-01-21 23:59:59").utcOffset(utcOffset, false);

function dateTimeMax(v) {
    var v1 = mustBeDateArray(v);
    if (v1.length === 0) {
        return minDateTime;
    } else {
        return moment.max(v1);
    }
}

function dateTimeMin(v) {
    var v1 = mustBeDateArray(v);
    if (v1.length === 0) {
        return maxDateTime;
    } else {
        return moment.min(v1);
    }
}

function dateTimeDurationAmount(v) {
    v = mustBeDuration(v);
    return natBox(v.asSeconds());
}

function dateTimeDurationFromString(stringDuration) {
    // TODO verify what the string format for durations is going to be.
    // Here we assume a number adjoined to a valid unit with a dash.
    if (typeof stringDuration === "string") {
	      var parts = stringDuration.split("-");
	      if (parts.length === 2) {
	          mustBeUnit(parts[1]);
            return moment.duration(parseFloat(parts[0]),parts[1]+"s");
        }
    }
    throw new Error("Not well formed duration input: " + stringDuration);
}

function dateTimePeriodFromString(stringDuration) {
    return dateTimeDurationFromString(stringDuration);
}

function dateTimeDurationFromNat(part, v) {
    mustBeUnit(part);
    var num = natUnbox(v);
    // 'quarters' not built into durations
    if (part === QUARTERS) {
        return moment.duration(num * 3,'months');
    } else {
        return moment.duration(num,part);
    }
}

function dateTimePeriodFromNat(part, v) {
    return dateTimeDurationFromNat(part, v);
}

function dateTimeAdd(date, duration) {
    date = mustBeDate(date);
    duration = mustBeDuration(duration);
    return date.add(duration);
}

function dateTimeSubtract(date, d) {
    date = mustBeDate(date);
    d = mustBeDuration(d);
    return date.subtract(d);
}

function dateTimeAddPeriod(date, period) {
    date = mustBeDate(date);
    period = mustBeDuration(period);
    return date.add(period);
}

function dateTimeSubtractPeriod(date, period) {
    date = mustBeDate(date);
    period = mustBeDuration(period);
    return date.subtract(period);
}

function dateTimeIsSame(date1, date2) {
    return compareDates(date1, date2) === 0;
}

function dateTimeIsBefore(date1, date2) {
    return compareDates(date1,date2) < 0;
}

function dateTimeIsAfter(date1, date2) {
    return compareDates(date1, date2) > 0;
}

function dateTimeDiff(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return moment.duration(date1.diff(date2,'seconds'),'seconds');
}

function dateTimeStartOf(part, date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf(part);
}

function dateTimeEndOf(part, date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.endOf(part);
}

/* DateTime Formating */
function dateTimeFormatFromString(s) {
  return s;
}
function dateTimeFormat(date,f) {
  date = mustBeDate(date);
  return date.format(f);
}
