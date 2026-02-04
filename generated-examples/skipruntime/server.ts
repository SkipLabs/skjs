// Server module: replaces @skipruntime/server for user code.
//
// Provides runService() that accepts safe-typed services and
// internally adapts them to the runtime format.

import type {
  SkipService,
  NamedInputDefinitions,
  NamedEagerCollections,
  Entry,
  Json,
  Context,
} from "./core.js";

import type { SkipService as RuntimeSkipService } from "@skipruntime/core";
import { runService as runtimeRunService } from "@skipruntime/server";

// ===================== Types =====================

export type ServiceOptions = {
  streaming_port: number;
  control_port: number;
  platform?: "wasm" | "native";
  no_cors?: boolean;
};

export type SkipServer = {
  close: () => Promise<void>;
};

// ===================== Internal Adaptation =====================

function adaptService<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends NamedEagerCollections,
  Resources,
>(
  safeService: SkipService<InputDefs, Inputs, ResourceInputs, Resources>,
): RuntimeSkipService<never, never> {
  // Extract initial data from service.inputs
  const initialData: Record<string, Entry<Json, Json>[]> = {};
  for (const name of Object.keys(safeService.inputs)) {
    const def = safeService.inputs[name] as { initial: Entry<Json, Json>[] } | undefined;
    if (def !== undefined) {
      initialData[name] = def.initial;
    }
  }

  return {
    initialData,

    resources: safeService.resources,

    createGraph(runtimeInputs: unknown, context: unknown): unknown {
      return safeService.createGraph(
        runtimeInputs as Inputs,
        context as Context,
      );
    },
  } as unknown as RuntimeSkipService<never, never>;
}

// ===================== Public API =====================

/**
 * Runs a safe-typed Skip service.
 *
 * @param service - The service using safe bindings
 * @param options - Server options (ports, etc.)
 */
export function runService<
  InputDefs extends NamedInputDefinitions,
  Inputs extends NamedEagerCollections,
  ResourceInputs extends NamedEagerCollections,
  Resources,
>(
  service: SkipService<InputDefs, Inputs, ResourceInputs, Resources>,
  options?: ServiceOptions,
): Promise<SkipServer> {
  const adapted = adaptService(service);
  return runtimeRunService(adapted, options);
}
