import type {
  EagerCollection,

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
  WebhookId,
  WebhookValue,
  DeliveryId,
  DeliveryValue,
  WebhookStatsId,
  WebhookStatsValue,
  WebhooksDeliveriesResourceParams,
} from "./types.js";

export type DeliveryAggregateInput = {
  status: "pending" | "success" | "failed";
  attemptedAt: number;
};

export type StatsAccum = {
  totalDeliveries: number;
  successCount: number;
  failureCount: number;
  lastDeliveryAt: number | null;
};

export type Inputs = {
  webhooks: InputDefinition<WebhookId, WebhookValue>;
  deliveries: InputDefinition<DeliveryId, DeliveryValue>;
};

export type InputCollections = {
  webhooks: EagerCollection<WebhookId, WebhookValue>;
  deliveries: EagerCollection<DeliveryId, DeliveryValue>;
};

export type GraphCollections = {
  webhooks: EagerCollection<WebhookId, WebhookValue>;
  deliveries: EagerCollection<DeliveryId, DeliveryValue>;
  stats: EagerCollection<WebhookStatsId, WebhookStatsValue>;
};

export type Resources = {
  "webhooks": ResourceClass<GraphCollections, {}>;
  "deliveries": ResourceClass<GraphCollections, {}>;
  "webhooks-deliveries": ResourceClass<GraphCollections, WebhooksDeliveriesResourceParams>;
  "stats": ResourceClass<GraphCollections, {}>;
};

export class DeliveryToWebhookKeyMapper implements Mapper<DeliveryId, DeliveryValue, string, DeliveryAggregateInput> {
  constructor() {
  }

  mapEntry(
    _key: DeliveryId,
    values: Values<DeliveryValue>,
    _context: Context
  ): Iterable<[string, DeliveryAggregateInput]> {
    const result: Array<[string, DeliveryAggregateInput]> = Array.of();
    for (const v of values) {
      const output: DeliveryAggregateInput = {
        status: v.status,
        attemptedAt: v.attemptedAt
      };
      result.push([v.webhookId, output]);
    }
    return result;
  }
}

export class StatsAccumToValueMapper implements Mapper<string, StatsAccum, WebhookStatsId, WebhookStatsValue> {
  constructor() {
  }

  mapEntry(
    key: string,
    values: Values<StatsAccum>,
    _context: Context
  ): Iterable<[WebhookStatsId, WebhookStatsValue]> {
    const result: Array<[WebhookStatsId, WebhookStatsValue]> = Array.of();
    for (const v of values) {
      const statsValue: WebhookStatsValue = {
        webhookId: key,
        totalDeliveries: v.totalDeliveries,
        successCount: v.successCount,
        failureCount: v.failureCount,
        lastDeliveryAt: v.lastDeliveryAt
      };
      result.push([key, statsValue]);
    }
    return result;
  }
}

export class FilterDeliveriesByWebhookMapper implements Mapper<DeliveryId, DeliveryValue, DeliveryId, DeliveryValue> {
  private webhookId: string;

  constructor(webhookId: string) {
    this.webhookId = webhookId;
  }

  mapEntry(
    key: DeliveryId,
    values: Values<DeliveryValue>,
    _context: Context
  ): Iterable<[DeliveryId, DeliveryValue]> {
    const result: Array<[DeliveryId, DeliveryValue]> = Array.of();
    for (const v of values) {
      if (v.webhookId === this.webhookId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class DeliveryStatsReducer implements Reducer<DeliveryAggregateInput, StatsAccum> {
  initial: Nullable<StatsAccum> = null;

  constructor() {
  }

  add(accum: Nullable<StatsAccum>, value: DeliveryAggregateInput & DepSafe): StatsAccum {
    if (accum === null) {
      return {
        totalDeliveries: 1,
        successCount: value.status === "success" ? 1 : 0,
        failureCount: value.status === "failed" ? 1 : 0,
        lastDeliveryAt: value.attemptedAt
      };
    }
    const lastDeliveryAt = accum.lastDeliveryAt;
    const newLastDeliveryAt = lastDeliveryAt === null
      ? value.attemptedAt
      : (value.attemptedAt > lastDeliveryAt ? value.attemptedAt : lastDeliveryAt);
    return {
      totalDeliveries: accum.totalDeliveries + 1,
      successCount: accum.successCount + (value.status === "success" ? 1 : 0),
      failureCount: accum.failureCount + (value.status === "failed" ? 1 : 0),
      lastDeliveryAt: newLastDeliveryAt
    };
  }

  remove(accum: StatsAccum, value: DeliveryAggregateInput & DepSafe): Nullable<StatsAccum> {
    const newTotal = accum.totalDeliveries - 1;
    if (newTotal <= 0) {
      return null;
    }
    const newSuccessCount = accum.successCount - (value.status === "success" ? 1 : 0);
    const newFailureCount = accum.failureCount - (value.status === "failed" ? 1 : 0);
    if (accum.lastDeliveryAt === value.attemptedAt) {
      return null;
    }
    return {
      totalDeliveries: newTotal,
      successCount: newSuccessCount,
      failureCount: newFailureCount,
      lastDeliveryAt: accum.lastDeliveryAt
    };
  }
}

export class WebhooksResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<WebhookId, WebhookValue> {
    return cs.webhooks;
  }
}

export class DeliveriesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<DeliveryId, DeliveryValue> {
    return cs.deliveries;
  }
}

export class WebhooksDeliveriesResource implements Resource<GraphCollections> {
  private webhookId: string;

  constructor(params: WebhooksDeliveriesResourceParams) {
    this.webhookId = params.webhookId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<DeliveryId, DeliveryValue> {
    return cs.deliveries.map(FilterDeliveriesByWebhookMapper, this.webhookId);
  }
}

export class StatsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<WebhookStatsId, WebhookStatsValue> {
    return cs.stats;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
            this.inputs = { webhooks: new InputDefinition<WebhookId, WebhookValue>([]), deliveries: new InputDefinition<DeliveryId, DeliveryValue>([]) };
    this.resources = { 
      "webhooks": WebhooksResource, 
      "deliveries": DeliveriesResource, 
      "webhooks-deliveries": WebhooksDeliveriesResource, 
      "stats": StatsResource 
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const deliveryAggregates = inputs.deliveries.map(DeliveryToWebhookKeyMapper);
    const reducedStats = deliveryAggregates.reduce(DeliveryStatsReducer);
    const stats = reducedStats.map(StatsAccumToValueMapper);
    
    return { 
      webhooks: inputs.webhooks, 
      deliveries: inputs.deliveries, 
      stats: stats 
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
