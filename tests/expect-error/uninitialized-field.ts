// SKJS rejects class fields with no initializer when the class has no
// constructor. TS allows this with strictPropertyInitialization off.
class HasUninitializedField {
  // @skjs-expect-error Field 'value' has no initializer and is not assigned in the constructor
  value: number;
}
