// Test that fields require type annotations

// Class field without type annotation or initializer
class FieldWithoutAnnotation {
  // @skjs-expect-error Type annotation expected for 'field'
  // @skjs-expect-error Uninitialized field 'field'
  field;
}

// Class field without type annotation but with initializer
class FieldWithInitializerNoAnnotation {
  // @skjs-expect-error Type annotation expected for 'field'
  field = 5;
}

// Class fields with type annotations work correctly
class FieldsWithAnnotations {
  field: number = 5;
  optional?: boolean;
}

// Object type field without annotation
type ObjectWithoutAnnotations = {
  // @skjs-expect-error Type annotation expected for 'field'
  field;
};

function useObjectWithoutAnnotations(x: ObjectWithoutAnnotations): void {
  const y = x.field;
}

// Object type fields with annotations
type ObjectWithAnnotations = {
  field: number;
  optional?: string;
};
