// A service class that is an AnySkipService: its createGraph takes any
// NamedEagerCollections, as the erased interface asks. The instance meets it
// member by member: the fields `inputs` and `resources` (a dictionary of
// construct signatures), the writable dictionary `externalServices` at the
// readonly optional field, and the method `createGraph`.
import type {
  AnySkipService,
  Context,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  ResourceClass,
  SharedCollections,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

class Service {
  readonly inputs: NamedInputDefinitions = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<SharedCollections, never>;
  } = {};
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(
    inputs: NamedEagerCollections,
    _context: Context,
  ): SharedCollections {
    return inputs;
  }
}

export function make(): AnySkipService {
  return new Service();
}
