// SKJS rejects class fields with no initializer when the class has no
// constructor. TS allows this with strictPropertyInitialization off.
class HasUninitializedField {
  // @skjs-expect-error Uninitialized field 'value'
  value: number;
}
