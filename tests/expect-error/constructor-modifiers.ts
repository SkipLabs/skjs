// SKJS rejects accessibility modifiers on constructors. TS allows
// `private constructor()` (singleton pattern) so this is SKJS-only.
class PrivateConstructor {
  // @skjs-expect-error 'private' modifier cannot appear on a constructor
  private constructor() {}
}
