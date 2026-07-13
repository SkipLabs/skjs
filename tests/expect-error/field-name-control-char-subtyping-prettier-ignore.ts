// prettier-ignore
// Field names decode escapes (#771), so a name like "a\nb" holds a real
// newline. The subtyping "field is missing" detail interpolates the name
// directly. The fix routes the name through the shared escaper so the
// control char is escaped ("The field 'a\nb' is missing") instead of a
// raw newline that truncates the detail. (#808)
function missingControlCharField(): { "a\nb": 0 } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line4 The field 'a\nb' is missing
  return {};
}
