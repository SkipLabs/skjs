// prettier-ignore
// A decoded control character in a property key must be escaped in the
// "does not exist" diagnostic, not emitted raw (which corrupts the message).
// Follow-up to string-escape decoding (#771): the key "a\nb" decodes to a
// real newline. Pinned to the pre-fix behavior, where that raw newline
// truncated the reported message at "Property 'a"; the fix escapes it so
// the whole message survives.
function accessControlCharKey(o: { x: 0 }): 0 {
  // @skjs-expect-error Property 'a\nb' does not exist on this type
  return o["a\nb"];
}
