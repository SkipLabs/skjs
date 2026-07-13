// prettier-ignore
// Field names decode escapes (#771), so a name like "a\nb" holds a real
// newline. The subtyping "field is missing" detail interpolates the name
// directly, leaking the raw control char (#808). Pinned to the pre-fix
// behavior, where the raw newline truncates the detail at "The field 'a";
// the fix routes the name through the shared escaper.
function missingControlCharField(): { "a\nb": 0 } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  // @skjs-expect-error-line4 The field 'a
  return {};
}
