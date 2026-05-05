// SKJS rejects accessibility modifiers on constructors. TS allows
// `private constructor()` (singleton pattern) so this is SKJS-only.
class PrivateConstructor {
  // @skjs-expect-error Constructors cannot have modifiers
  private constructor() {}
}
