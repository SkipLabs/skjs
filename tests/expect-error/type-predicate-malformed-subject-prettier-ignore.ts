// prettier-ignore
// The subject of `is` is not validated yet: a malformed subject (anything
// other than a plain identifier, which is all TS grammar allows — this
// isn't valid TS syntax, hence the prettier-ignore) is currently accepted
// too.
declare function isBad(x: unknown): (number | string) is number;
