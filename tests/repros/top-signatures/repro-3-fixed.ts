// Fixed version of repro-3: NamedCollections constraint issue
//
// Changes from original library:
// - SkipService: removed "extends NamedCollections" constraints
// - Resource: parameterized by K, V instead of Collections
//
// Expected:
// - tsc: OK
// - skjs: OK

// ============== MODIFIED LIBRARY TYPES ==============

type Json = boolean | number | string | (Json | null)[] | JsonObject;

type JsonObject = { [key: string]: Json | null };

interface Context {}

interface EagerCollection<K extends Json, V extends Json> {
  getArray(key: K): V[];
}

// CHANGED: Resource now parameterized by K, V (not Collections extends NamedCollections)
interface Resource<K extends Json, V extends Json> {
  instantiate(context: Context): EagerCollection<K, V>;
}

// CHANGED: removed "extends NamedCollections" constraints
interface SkipService<Inputs, ResourceInputs> {
  resources: { [name: string]: new (params: Json) => Resource<Json, Json> };

  createGraph(inputCollections: Inputs, context: Context): ResourceInputs;
}

// ============== USER CODE (nearly identical to repro-3) ==============

type InputCollections = {
  metrics: EagerCollection<string, string>;
};

type ResourceInputs = InputCollections;

class Service implements SkipService<InputCollections, ResourceInputs> {
  // Keep this empty; the repro is about the generic constraints on InputCollections/ResourceInputs.
  resources: { [name: string]: new (params: Json) => Resource<Json, Json> } =
    {};

  createGraph(
    inputCollections: InputCollections,
    _context: Context,
  ): ResourceInputs {
    return inputCollections;
  }
}

function service(): SkipService<InputCollections, ResourceInputs> {
  return new Service();
}
