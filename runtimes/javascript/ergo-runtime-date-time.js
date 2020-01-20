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

/* JavaScript runtime for DateTime component */

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
function dateTimeGetSeconds(date) {
    date = mustBeDate(date);
    return boxNat(date.second());
}
function dateTimeGetMinutes(date) {
    date = mustBeDate(date);
    return boxNat(date.minute());
}
function dateTimeGetHours(date) {
    date = mustBeDate(date);
    return boxNat(date.hour());
}
function dateTimeGetDays(date) {
    date = mustBeDate(date);
    return boxNat(date.date());
}
function dateTimeGetWeeks(date) {
    date = mustBeDate(date);
    return boxNat(date.week());
}
function dateTimeGetMonths(date) {
    date = mustBeDate(date);
    return boxNat(date.month() + 1);
}
function dateTimeGetQuarters(date) {
    date = mustBeDate(date);
    return boxNat(date.quarter());
}
function dateTimeGetYears(date) {
    date = mustBeDate(date);
    return boxNat(date.year());
}

function dateTimeStartOfDay(date) {
    date = mustBeDate(date);
    return date.startOf('day');
}
function dateTimeStartOfWeek(date) {
    date = mustBeDate(date);
    return date.startOf('week');
}
function dateTimeStartOfMonth(date) {
    date = mustBeDate(date);
    return date.startOf('month');
}
function dateTimeStartOfQuarter(date) {
    date = mustBeDate(date);
    return date.startOf('quarter');
}
function dateTimeStartOfYear(date) {
    date = mustBeDate(date);
    return date.startOf('year');
}

function dateTimeEndOfDay(date) {
    date = mustBeDate(date);
    return date.endOf('day');
}
function dateTimeEndOfWeek(date) {
    date = mustBeDate(date);
    return date.endOf('week');
}
function dateTimeEndOfMonth(date) {
    date = mustBeDate(date);
    return date.endOf('month');
}
function dateTimeEndOfQuarter(date) {
    date = mustBeDate(date);
    return date.endOf('quarter');
}
function dateTimeEndOfYear(date) {
    date = mustBeDate(date);
    return date.endOf('year');
}
/* DateTime Formating */
function dateTimeFormatFromString(s) {
  return s;
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
    return boxNat(v.asSeconds());
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

function dateTimeDurationFromSeconds(v) {
    var num = unboxNat(v);
    return moment.duration(num,'second');
}
function dateTimeDurationFromMinutes(v) {
    var num = unboxNat(v);
    return moment.duration(num,'minute');
}
function dateTimeDurationFromHours(v) {
    var num = unboxNat(v);
    return moment.duration(num,'hour');
}
function dateTimeDurationFromDays(v) {
    var num = unboxNat(v);
    return moment.duration(num,'day');
}
function dateTimeDurationFromWeeks(v) {
    var num = unboxNat(v);
    return moment.duration(num,'week');
}

function dateTimePeriodFromString(stringDuration) {
    return dateTimeDurationFromString(stringDuration);
}
function dateTimePeriodFromDays(v) {
    var num = unboxNat(v);
    return moment.duration(num,'day');
}
function dateTimePeriodFromWeeks(v) {
    var num = unboxNat(v);
    return moment.duration(num,'week');
}
function dateTimePeriodFromMonths(v) {
    var num = unboxNat(v);
    return moment.duration(num,'month');
}
function dateTimePeriodFromQuarters(v) {
    var num = unboxNat(v);
    return moment.duration(num * 3,'month');
}
function dateTimePeriodFromYears(v) {
    var num = unboxNat(v);
    return moment.duration(num,'year');
}

function dateTimeFormat(date,f) {
  date = mustBeDate(date);
  return date.format(f);
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

