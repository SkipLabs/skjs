// Test that fields require type annotations

// Class field without type annotation or initializer
class FieldWithoutAnnotation {
  // @skjs-expect-error Field 'field' has no initializer and is not assigned in the constructor
  // @skjs-expect-error Member 'field' must have an explicit type annotation
  field;
}

// Class field without type annotation but with initializer
class FieldWithInitializerNoAnnotation {
  // @skjs-expect-error Member 'field' must have an explicit type annotation
  field = 5;
}

// Class fields with type annotations work correctly
class FieldsWithAnnotations {
  field: number = 5;
  optional?: boolean;
}

// Object type field without annotation
type ObjectWithoutAnnotations = {
  // @skjs-expect-error Member 'field' must have an explicit type annotation
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
