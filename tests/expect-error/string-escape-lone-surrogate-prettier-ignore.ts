// prettier-ignore
// A lone (unpaired) surrogate escape. tsc accepts it as a lone UTF-16 code
// unit, but a Skip Char cannot represent a surrogate, so skjs rejects it
// (sound, stricter than tsc). Pinned first to the buggy pre-fix behavior.
type T = "\uD800";
