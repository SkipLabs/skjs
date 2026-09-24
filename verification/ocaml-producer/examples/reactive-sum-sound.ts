import type {
  Context,
  EagerCollection,
  ExternalService,
  Mapper,
  NamedEagerCollections,
  NamedInputDefinitions,
  Resource,
  ResourceClass,
  SkipService,
  Values,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

import { runService } from "@skipruntime/server";

const platform: "wasm" | "native" =
  process.env["SKIP_PLATFORM"] === "native" ? "native" : "wasm";

class AddIndex implements Mapper<string, number, string, [number, number]> {
  constructor(private index: number) {}

  mapEntry(
    key: string,
    values: Values<number>,
  ): Iterable<[string, [number, number]]> {
    return [[key, [this.index, values.getUnique()]]];
  }
}

class Plus implements Mapper<string, number, string, number> {
  mapEntry(key: string, values: Values<number>): Iterable<[string, number]> {
    return [[key, values.toArray().reduce((p: number, c: number) => p + c, 0)]];
  }
}

class Minus implements Mapper<string, [number, number], string, number> {
  mapEntry(
    key: string,
    values: Values<[number, number]>,
  ): Iterable<[string, number]> {
    const acc = (p: number | null, c: [number, number]) => {
      return p !== null ? p - c[1] : c[1];
    };
    return [
      [key, values.toArray().sort().reduce<number | null>(acc, null) ?? 0],
    ];
  }
}

interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
  readonly input2: EagerCollection<string, number>;
}

class Add implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1.merge(cs.input2).map(Plus);
  }
}

class Sub implements Resource<Collections> {
  instantiate(cs: Collections): EagerCollection<string, number> {
    return cs.input1
      .map(AddIndex, 0)
      .merge(cs.input2.map(AddIndex, 1))
      .map(Minus);
  }
}

interface Inputs extends NamedInputDefinitions {
  readonly input1: InputDefinition<string, number>;
  readonly input2: InputDefinition<string, number>;
}

class Service implements SkipService<Inputs, Collections, Collections> {
  readonly inputs: Inputs = {
    input1: new InputDefinition<string, number>(),
    input2: new InputDefinition<string, number>(),
  };
  readonly resources: {
    readonly [name: string]: ResourceClass<Collections, never>;
  } = { add: Add, sub: Sub };
  externalServices: { [name: string]: ExternalService } = {};

  createGraph(inputs: Collections, _context: Context): Collections {
    return inputs;
  }
}

async function main(): Promise<void> {
  const server = await runService(new Service(), {
    control_port: 3588,
    streaming_port: 3587,
    platform,
  });
  const shutdown = async (): Promise<void> => {
    await server.close();
  };
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
}

await main();
