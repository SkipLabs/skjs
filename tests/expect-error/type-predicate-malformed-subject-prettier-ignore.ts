// prettier-ignore
// The subject of `is` is shape-checked: it must be a plain identifier, the
// only form TS grammar allows (this isn't valid TS syntax itself, hence the
// prettier-ignore).
// @skjs-expect-error A type predicate's subject must be an identifier
declare function isBad(x: unknown): (number | string) is number;
