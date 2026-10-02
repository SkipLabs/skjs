// sum.ts's createGraph is not AnySkipService's: it takes the named
// collections `Collections`, and the erased interface may pass any
// NamedEagerCollections, one without `input1`. TypeScript accepts the
// service through its bivariant method parameters.
import type {
  AnySkipService,
  Context,
  EagerCollection,
  ExternalService,
  NamedEagerCollections,
  NamedInputDefinitions,
  ResourceClass,
  SharedCollections,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
}

class Service {
  readonly inputs: NamedInputDefinitions = {
    input1: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<SharedCollections, never>;
  } = {};
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: Collections, _context: Context): SharedCollections {
    return inputs;
  }
}

export function make(): AnySkipService {
  return new Service();
}
