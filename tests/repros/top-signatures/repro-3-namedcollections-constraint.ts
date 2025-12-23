// Repro for SKJS signature:
// "Constraint not satisfied :: This is of type: <TYPE> | It does not implement: NamedCollections"
//
// This uses the real @skipruntime/core type definitions (via tsconfig paths mapping)
// because the mismatch depends on the runtime stubs' exact types.
//
// Expected:
// - tsc: OK
// - skjs: Constraint not satisfied ... InputCollections ... NamedCollections

import type { EagerCollection, SkipService, Context, Json, Resource } from "@skipruntime/core";

type InputCollections = {
  metrics: EagerCollection<string, string>;
};

type ResourceInputs = InputCollections;

class Service implements SkipService<InputCollections, ResourceInputs> {
  // Keep this empty; the repro is about the generic constraints on InputCollections/ResourceInputs.
  resources: { [name: string]: new (params: Json) => Resource<ResourceInputs> } = {};

  createGraph(inputCollections: InputCollections, _context: Context): ResourceInputs {
    return inputCollections;
  }
}

function service(): SkipService<InputCollections, ResourceInputs> {
  return new Service();
}


