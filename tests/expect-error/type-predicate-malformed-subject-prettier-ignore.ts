// prettier-ignore
// The subject of `is` must name a parameter of the enclosing function (or
// `this`) — this isn't valid TS syntax itself, hence the prettier-ignore.
// @skjs-expect-error A type predicate's subject must be a parameter of the enclosing function, or 'this'
declare function isBad(x: unknown): (number | string) is number;
