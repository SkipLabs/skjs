import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  MetricId,
  MetricValue,
} from "./types.js";


export type Inputs = {
  metrics: InputDefinition<MetricId, MetricValue>;
};

export type InputCollections = {
  metrics: EagerCollection<MetricId, MetricValue>;
};

export type OrderedMetricKey = [number, MetricId];

export type GraphCollections = {
  metrics: EagerCollection<OrderedMetricKey, MetricValue>;
};

export type Resources = {
  readonly "metrics": ResourceClass<GraphCollections, {}>;
};

class OrderByTimestampMapper implements Mapper<MetricId, MetricValue, OrderedMetricKey, MetricValue> {
  mapEntry(
    key: MetricId,
    values: Values<MetricValue>,
    _context: Context
  ): Iterable<[OrderedMetricKey, MetricValue]> {
    const result: Array<[OrderedMetricKey, MetricValue]> = Array.of();
    for (const v of values) {
      const orderedKey: OrderedMetricKey = [v.timestamp, key];
      result.push([orderedKey, v]);
    }
    return result;
  }
}

export class MetricsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<OrderedMetricKey, MetricValue> {
    return cs.metrics;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { metrics: new InputDefinition<MetricId, MetricValue>([]) };
    this.resources = { "metrics": MetricsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const orderedMetrics = inputs.metrics.map(OrderByTimestampMapper);
    return { metrics: orderedMetrics };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
