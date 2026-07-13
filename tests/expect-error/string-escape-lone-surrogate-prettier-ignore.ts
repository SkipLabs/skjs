// prettier-ignore
// A lone (unpaired) surrogate escape. tsc accepts it as a lone UTF-16 code
// unit, but a Skip Char cannot represent a surrogate, so skjs rejects it
// (sound, stricter than tsc).
// @skjs-expect-error Unpaired surrogate escape sequences are not supported
type T = "\uD800";
