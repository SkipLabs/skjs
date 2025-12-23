// Repro for SKJS signature:
// "Constraint not satisfied :: This is of type: <TYPE> | It does not implement: Json"
//
// Root cause hypothesis:
// - SKJS currently fails to recognize that ordinary object types (including those with string index signatures)
//   are valid Json via a recursive Json definition.
//
// Expected:
// - tsc: OK
// - skjs: "Constraint not satisfied" / "It does not implement: Json"

// Match the recursive shape from import-stubs/@skipruntime/core/index.d.ts
type Json = boolean | number | string | (Json | null)[] | JsonObject;
type JsonObject = { [key: string]: Json | null };

interface EagerCollection<K extends Json, V extends Json> {
  getArray(key: K): V[];
}

type MetricData = {
  name: string;
  value: number;
  tags: { [name: string]: string };
};

// Should satisfy V extends Json in TypeScript (MetricData is a JsonObject).
type Collections = {
  metrics: EagerCollection<string, MetricData>;
};

// Force the constraint to be checked:
declare function useCollections<
  C extends { [name: string]: EagerCollection<Json, Json> },
>(c: C): void;

function test(): void {
  // Avoid SKJS top-level constant restrictions: keep object literals inside a function.
  const collections: Collections = {
    metrics: {
      getArray(_key: string): MetricData[] {
        const out: MetricData[] = Array.of();
        return out;
      },
    },
  };

  useCollections(collections);
}

test();
