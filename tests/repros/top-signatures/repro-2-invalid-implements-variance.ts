// Repro for SKJS top signature:
// "Invalid implements :: This is of type boolean | It is incompatible with: <TYPE>"
//
// Root cause hypothesis:
// - TypeScript treats *method parameters* in interfaces as bivariant (unsound), so this passes.
// - SKJS appears to use sounder variance checking, so the implementation is rejected.
//
// Expected:
// - tsc: OK
// - skjs: "Invalid implements" with a follow-up like "This is of type boolean" / "It is incompatible with: string"

// Minimal Json type (enough to include boolean + string)
type Json = boolean | number | string;

// Interface with a method parameter that makes K appear in parameter position.
// In TypeScript, method parameters are bivariant for assignability of method types.
interface EagerCollection<K extends Json, V extends Json> {
  getArray(key: K): V[];
}

// Generic interface similar to @skipruntime/core's Resource:
// it expects an EagerCollection<Json, Json>.
interface Resource {
  instantiate(): EagerCollection<Json, Json>;
}

// This "implements" is the key:
// The method returns EagerCollection<string, Json>, which is not soundly assignable to EagerCollection<Json, Json>
// because Json includes boolean but string-only collections can't accept boolean keys.
class BadResource implements Resource {
  instantiate(): EagerCollection<string, Json> {
    return {
      getArray(_key: string): Json[] {
        return [];
      },
    };
  }
}


