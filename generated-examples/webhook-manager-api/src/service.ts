import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "@skipruntime/core";

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

type Inputs = {
  webhooks: Entry<WebhookId, WebhookValue>[];
  deliveries: Entry<DeliveryId, DeliveryValue>[];
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

type Resources = {
  "webhooks": new (params: Json) => Resource<GraphCollections>;
  "deliveries": new (params: Json) => Resource<GraphCollections>;
  "webhooks-deliveries": new (params: Json) => Resource<GraphCollections>;
  "stats": new (params: Json) => Resource<GraphCollections>;
};

export class DeliveryToWebhookKeyMapper implements Mapper<DeliveryId, DeliveryValue, string, DeliveryAggregateInput> {
  constructor() {
  }

  mapEntry(
    _key: DeliveryId,
    values: Values<DeliveryValue>,
    _context: Context
  ): Iterable<[string, DeliveryAggregateInput]> {
    const arr = values.toArray();
    const result: Array<[string, DeliveryAggregateInput]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[WebhookStatsId, WebhookStatsValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[DeliveryId, DeliveryValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const newLastDeliveryAt = accum.lastDeliveryAt === null 
      ? value.attemptedAt 
      : (value.attemptedAt > accum.lastDeliveryAt ? value.attemptedAt : accum.lastDeliveryAt);
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
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<WebhookId, WebhookValue> {
    return cs.webhooks;
  }
}

export class DeliveriesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
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

  constructor(params: Json) {
    const typed = params as WebhooksDeliveriesResourceParams;
    this.webhookId = typed.webhookId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<DeliveryId, DeliveryValue> {
    return cs.deliveries.map(FilterDeliveriesByWebhookMapper, this.webhookId);
  }
}

export class StatsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<WebhookStatsId, WebhookStatsValue> {
    return cs.stats;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyWebhooks: Entry<WebhookId, WebhookValue>[] = Array.of();
    const emptyDeliveries: Entry<DeliveryId, DeliveryValue>[] = Array.of();
    this.initialData = { webhooks: emptyWebhooks, deliveries: emptyDeliveries };
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
