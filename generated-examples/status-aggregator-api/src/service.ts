import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  ComponentId,
  ComponentValue,
  SystemStatusId,
  SystemStatusValue,
  HealthyDegradedUnhealthyEnum,
} from "./types.js";

export type ComponentStatus = HealthyDegradedUnhealthyEnum;

export type StatusCount = {
  status: ComponentStatus;
  lastChecked: number;
};

export type StatusAccum = {
  componentCount: number;
  healthyCount: number;
  degradedCount: number;
  unhealthyCount: number;
  lastUpdated: number;
};

export type Inputs = {
  components: InputDefinition<ComponentId, ComponentValue>;
};

export type InputCollections = {
  components: EagerCollection<ComponentId, ComponentValue>;
};

export type GraphCollections = {
  components: EagerCollection<ComponentId, ComponentValue>;
  systemStatus: EagerCollection<SystemStatusId, SystemStatusValue>;
};

export type Resources = {
  readonly "status": ResourceClass<GraphCollections, {}>;
  readonly "components": ResourceClass<GraphCollections, {}>;
  readonly "components-healthy": ResourceClass<GraphCollections, {}>;
  readonly "components-degraded": ResourceClass<GraphCollections, {}>;
  readonly "components-unhealthy": ResourceClass<GraphCollections, {}>;
};

export class ComponentToStatusMapper implements Mapper<ComponentId, ComponentValue, SystemStatusId, StatusCount> {
  constructor() {
  }

  mapEntry(
    _key: ComponentId,
    values: Values<ComponentValue>,
    _context: Context
  ): Iterable<[SystemStatusId, StatusCount]> {
    const result: Array<[SystemStatusId, StatusCount]> = Array.of();
    for (const v of values) {
      const statusCount: StatusCount = {
        status: v.status,
        lastChecked: v.lastChecked
      };
      result.push(["system", statusCount]);
    }
    return result;
  }
}

export class StatusAccumToSystemStatusMapper implements Mapper<SystemStatusId, StatusAccum, SystemStatusId, SystemStatusValue> {
  constructor() {
  }

  mapEntry(
    key: SystemStatusId,
    values: Values<StatusAccum>,
    _context: Context
  ): Iterable<[SystemStatusId, SystemStatusValue]> {
    const result: Array<[SystemStatusId, SystemStatusValue]> = Array.of();
    for (const accum of values) {
      const overallStatus: HealthyDegradedUnhealthyEnum =
        accum.unhealthyCount > 0 ? "unhealthy" :
        accum.degradedCount > 0 ? "degraded" :
        "healthy";
      const systemStatusValue: SystemStatusValue = {
        overallStatus: overallStatus,
        componentCount: accum.componentCount,
        healthyCount: accum.healthyCount,
        degradedCount: accum.degradedCount,
        unhealthyCount: accum.unhealthyCount,
        lastUpdated: accum.lastUpdated
      };
      result.push([key, systemStatusValue]);
    }
    return result;
  }
}

export class FilterByStatusMapper implements Mapper<ComponentId, ComponentValue, ComponentId, ComponentValue> {
  private targetStatus: ComponentStatus;

  constructor(targetStatus: ComponentStatus) {
    this.targetStatus = targetStatus;
  }

  mapEntry(
    key: ComponentId,
    values: Values<ComponentValue>,
    _context: Context
  ): Iterable<[ComponentId, ComponentValue]> {
    const result: Array<[ComponentId, ComponentValue]> = Array.of();
    for (const v of values) {
      if (v.status === this.targetStatus) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class StatusAggregatorReducer implements Reducer<StatusCount, StatusAccum> {
  initial: Nullable<StatusAccum> = null;

  constructor() {
  }

  add(accum: Nullable<StatusAccum>, value: StatusCount & DepSafe): StatusAccum {
    if (accum === null) {
      const healthyCount = value.status === "healthy" ? 1 : 0;
      const degradedCount = value.status === "degraded" ? 1 : 0;
      const unhealthyCount = value.status === "unhealthy" ? 1 : 0;
      return {
        componentCount: 1,
        healthyCount: healthyCount,
        degradedCount: degradedCount,
        unhealthyCount: unhealthyCount,
        lastUpdated: value.lastChecked
      };
    }
    const healthyInc = value.status === "healthy" ? 1 : 0;
    const degradedInc = value.status === "degraded" ? 1 : 0;
    const unhealthyInc = value.status === "unhealthy" ? 1 : 0;
    const newLastUpdated = value.lastChecked > accum.lastUpdated ? value.lastChecked : accum.lastUpdated;
    return {
      componentCount: accum.componentCount + 1,
      healthyCount: accum.healthyCount + healthyInc,
      degradedCount: accum.degradedCount + degradedInc,
      unhealthyCount: accum.unhealthyCount + unhealthyInc,
      lastUpdated: newLastUpdated
    };
  }

  remove(accum: StatusAccum, value: StatusCount & DepSafe): Nullable<StatusAccum> {
    const healthyDec = value.status === "healthy" ? 1 : 0;
    const degradedDec = value.status === "degraded" ? 1 : 0;
    const unhealthyDec = value.status === "unhealthy" ? 1 : 0;
    const newComponentCount = accum.componentCount - 1;
    if (newComponentCount <= 0) {
      return null;
    }
    return {
      componentCount: newComponentCount,
      healthyCount: accum.healthyCount - healthyDec,
      degradedCount: accum.degradedCount - degradedDec,
      unhealthyCount: accum.unhealthyCount - unhealthyDec,
      lastUpdated: accum.lastUpdated
    };
  }
}

export class StatusResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<SystemStatusId, SystemStatusValue> {
    return cs.systemStatus;
  }
}

export class ComponentsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ComponentId, ComponentValue> {
    return cs.components;
  }
}

export class ComponentsHealthyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ComponentId, ComponentValue> {
    return cs.components.map(FilterByStatusMapper, "healthy");
  }
}

export class ComponentsDegradedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ComponentId, ComponentValue> {
    return cs.components.map(FilterByStatusMapper, "degraded");
  }
}

export class ComponentsUnhealthyResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ComponentId, ComponentValue> {
    return cs.components.map(FilterByStatusMapper, "unhealthy");
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { components: new InputDefinition<ComponentId, ComponentValue>([]) };
    this.resources = {
      "status": StatusResource,
      "components": ComponentsResource,
      "components-healthy": ComponentsHealthyResource,
      "components-degraded": ComponentsDegradedResource,
      "components-unhealthy": ComponentsUnhealthyResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const statusCounts = inputs.components.map(ComponentToStatusMapper);
    const statusAccum = statusCounts.reduce(StatusAggregatorReducer);
    const systemStatus = statusAccum.map(StatusAccumToSystemStatusMapper);
    return {
      components: inputs.components,
      systemStatus: systemStatus
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
