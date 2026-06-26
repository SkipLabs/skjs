import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  CustomerId,
  CustomerValue,
  PlanId,
  PlanValue,
  SubscriptionId,
  SubscriptionValue,
  SubscriptionsByCustomerResourceParams,
} from "./types.js";


export type Inputs = {
  customers: InputDefinition<CustomerId, CustomerValue>;
  plans: InputDefinition<PlanId, PlanValue>;
  subscriptions: InputDefinition<SubscriptionId, SubscriptionValue>;
};

export type InputCollections = {
  customers: EagerCollection<CustomerId, CustomerValue>;
  plans: EagerCollection<PlanId, PlanValue>;
  subscriptions: EagerCollection<SubscriptionId, SubscriptionValue>;
};

export type GraphCollections = {
  customers: EagerCollection<CustomerId, CustomerValue>;
  plans: EagerCollection<PlanId, PlanValue>;
  subscriptions: EagerCollection<SubscriptionId, SubscriptionValue>;
};

export type Resources = {
  readonly "customers": ResourceClass<GraphCollections, {}>;
  readonly "plans": ResourceClass<GraphCollections, {}>;
  readonly "subscriptions": ResourceClass<GraphCollections, {}>;
  readonly "subscriptions-active": ResourceClass<GraphCollections, {}>;
  readonly "subscriptions-by-customer": ResourceClass<GraphCollections, SubscriptionsByCustomerResourceParams>;
  readonly "subscriptions-expiring-soon": ResourceClass<GraphCollections, {}>;
};

export class ActiveSubscriptionFilterMapper implements Mapper<SubscriptionId, SubscriptionValue, SubscriptionId, SubscriptionValue> {
  constructor() {
  }

  mapEntry(
    key: SubscriptionId,
    values: Values<SubscriptionValue>,
    _context: Context
  ): Iterable<[SubscriptionId, SubscriptionValue]> {
    const result: Array<[SubscriptionId, SubscriptionValue]> = Array.of();
    for (const v of values) {
      if (v.status === "active") {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class SubscriptionByCustomerFilterMapper implements Mapper<SubscriptionId, SubscriptionValue, SubscriptionId, SubscriptionValue> {
  private customerId: string;

  constructor(customerId: string) {
    this.customerId = customerId;
  }

  mapEntry(
    key: SubscriptionId,
    values: Values<SubscriptionValue>,
    _context: Context
  ): Iterable<[SubscriptionId, SubscriptionValue]> {
    const result: Array<[SubscriptionId, SubscriptionValue]> = Array.of();
    for (const v of values) {
      if (v.customerId === this.customerId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class ExpiringSoonFilterMapper implements Mapper<SubscriptionId, SubscriptionValue, SubscriptionId, SubscriptionValue> {
  private now: number;
  private thirtyDaysFromNow: number;

  constructor(now: number = Date.now()) {
    this.now = now;
    const thirtyDaysMs = 30 * 24 * 60 * 60 * 1000;
    this.thirtyDaysFromNow = now + thirtyDaysMs;
  }

  mapEntry(
    key: SubscriptionId,
    values: Values<SubscriptionValue>,
    _context: Context
  ): Iterable<[SubscriptionId, SubscriptionValue]> {
    const result: Array<[SubscriptionId, SubscriptionValue]> = Array.of();
    for (const v of values) {
      if (v.endDate >= this.now && v.endDate <= this.thirtyDaysFromNow) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class CustomersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CustomerId, CustomerValue> {
    return cs.customers;
  }
}

export class PlansResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<PlanId, PlanValue> {
    return cs.plans;
  }
}

export class SubscriptionsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<SubscriptionId, SubscriptionValue> {
    return cs.subscriptions;
  }
}

export class SubscriptionsActiveResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<SubscriptionId, SubscriptionValue> {
    return cs.subscriptions.map(ActiveSubscriptionFilterMapper);
  }
}

export class SubscriptionsByCustomerResource implements Resource<GraphCollections> {
  private customerId: string;

  constructor(params: SubscriptionsByCustomerResourceParams) {
    this.customerId = params.customerId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<SubscriptionId, SubscriptionValue> {
    return cs.subscriptions.map(SubscriptionByCustomerFilterMapper, this.customerId);
  }
}

export class SubscriptionsExpiringSoonResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<SubscriptionId, SubscriptionValue> {
    const now = Date.now();
    return cs.subscriptions.map(ExpiringSoonFilterMapper, now);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                this.inputs = { customers: new InputDefinition<CustomerId, CustomerValue>([]), plans: new InputDefinition<PlanId, PlanValue>([]), subscriptions: new InputDefinition<SubscriptionId, SubscriptionValue>([]) };
    this.resources = { "customers": CustomersResource, "plans": PlansResource, "subscriptions": SubscriptionsResource, "subscriptions-active": SubscriptionsActiveResource, "subscriptions-by-customer": SubscriptionsByCustomerResource, "subscriptions-expiring-soon": SubscriptionsExpiringSoonResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { customers: inputs.customers, plans: inputs.plans, subscriptions: inputs.subscriptions };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
