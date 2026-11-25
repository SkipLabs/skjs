// Access modifiers on merged interface re-declarations (SKJS allows 'private'
// in an interface, unlike tsc's TS1070, so this file is prettier-ignored):
// re-declaring a 'private' member without it must not silently become public
// in the merged interface — tsc reports TS2687 for the modifier mismatch.
interface Access {
  private x: number;
}
interface Access {
  // @skjs-expect-error All declarations of 'x' must have identical modifiers.
  x: number;
}
