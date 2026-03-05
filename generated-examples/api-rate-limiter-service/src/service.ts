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
  RateLimitConfigId,
  RateLimitConfigValue,
  RequestEventId,
  RequestEventValue,
  RateLimitStatusId,
  RateLimitStatusValue,
  ClientStatusId,
  ClientStatusValue,
} from "./types.js";

export type RequestCountAccum = {
  count: number;
  latestTimestamp: number;
};

export type ClientAggregateInput = {
  requestCount: number;
  isLimited: number;
};

export type ClientAggregateAccum = {
  totalRequests: number;
  limitedEndpoints: number;
};

export type Inputs = {
  rateLimitConfigs: InputDefinition<RateLimitConfigId, RateLimitConfigValue>;
  requestEvents: InputDefinition<RequestEventId, RequestEventValue>;
};

export type InputCollections = {
  rateLimitConfigs: EagerCollection<RateLimitConfigId, RateLimitConfigValue>;
  requestEvents: EagerCollection<RequestEventId, RequestEventValue>;
};

export type GraphCollections = {
  rateLimitConfigs: EagerCollection<RateLimitConfigId, RateLimitConfigValue>;
  requestEvents: EagerCollection<RequestEventId, RequestEventValue>;
  rateLimitStatus: EagerCollection<RateLimitStatusId, RateLimitStatusValue>;
  clientStatus: EagerCollection<ClientStatusId, ClientStatusValue>;
};

// Using object instead of tuple as readonly tuples are not yet supported by skjs.
export type ClientEndpointKey = {
  clientId: string;
  endpoint: string;
};

export type Resources = {
  readonly "rateLimitStatus": ResourceClass<GraphCollections, {}>;
  readonly "clientStatus": ResourceClass<GraphCollections, {}>;
};

export class RequestEventToClientEndpointMapper implements Mapper<RequestEventId, RequestEventValue, ClientEndpointKey, RequestEventValue> {
  constructor() {
  }

  mapEntry(
    _key: RequestEventId,
    values: Values<RequestEventValue>,
    _context: Context
  ): Iterable<[ClientEndpointKey, RequestEventValue]> {
    const result: Array<[ClientEndpointKey, RequestEventValue]> = Array.of();
    for (const v of values) {
      const compositeKey: ClientEndpointKey = { clientId: v.clientId, endpoint: v.endpoint };
      result.push([compositeKey, v]);
    }
    return result;
  }
}

export class RequestCountToRateLimitStatusMapper implements Mapper<ClientEndpointKey, RequestCountAccum, RateLimitStatusId, RateLimitStatusValue> {
  private configs: EagerCollection<RateLimitConfigId, RateLimitConfigValue>;

  constructor(configs: EagerCollection<RateLimitConfigId, RateLimitConfigValue>) {
    this.configs = configs;
  }

  mapEntry(
    key: ClientEndpointKey,
    values: Values<RequestCountAccum>,
    _context: Context
  ): Iterable<[RateLimitStatusId, RateLimitStatusValue]> {
    const result: Array<[RateLimitStatusId, RateLimitStatusValue]> = Array.of();
    const clientId = key.clientId;
    const endpoint = key.endpoint;

    for (const accum of values) {
      const configArr = this.configs.getArray(endpoint);

      let maxRequests = 100;
      let windowMs = 60000;

      const config = configArr[0];
      if (config !== undefined) {
        maxRequests = config.maxRequests;
        windowMs = config.windowMs;
      }
      
      const currentCount = accum.count;
      const remainingRequests = maxRequests - currentCount > 0 ? maxRequests - currentCount : 0;
      const isLimited = currentCount >= maxRequests ? 1 : 0;
      
      const windowResetAt = accum.latestTimestamp + windowMs;
      
      const statusId: RateLimitStatusId = JSON.stringify([clientId, endpoint]);
      const statusValue: RateLimitStatusValue = {
        clientId: clientId,
        endpoint: endpoint,
        currentCount: currentCount,
        maxRequests: maxRequests,
        windowMs: windowMs,
        remainingRequests: remainingRequests,
        isLimited: isLimited,
        windowResetAt: windowResetAt
      };
      
      result.push([statusId, statusValue]);
    }
    return result;
  }
}

export class RateLimitStatusToClientMapper implements Mapper<RateLimitStatusId, RateLimitStatusValue, ClientStatusId, ClientAggregateInput> {
  constructor() {
  }

  mapEntry(
    _key: RateLimitStatusId,
    values: Values<RateLimitStatusValue>,
    _context: Context
  ): Iterable<[ClientStatusId, ClientAggregateInput]> {
    const result: Array<[ClientStatusId, ClientAggregateInput]> = Array.of();
    for (const v of values) {
      const clientId: ClientStatusId = v.clientId;
      const input: ClientAggregateInput = {
        requestCount: v.currentCount,
        isLimited: v.isLimited
      };
      result.push([clientId, input]);
    }
    return result;
  }
}

export class ClientAggregateToStatusMapper implements Mapper<ClientStatusId, ClientAggregateAccum, ClientStatusId, ClientStatusValue> {
  constructor() {
  }

  mapEntry(
    key: ClientStatusId,
    values: Values<ClientAggregateAccum>,
    _context: Context
  ): Iterable<[ClientStatusId, ClientStatusValue]> {
    const result: Array<[ClientStatusId, ClientStatusValue]> = Array.of();
    for (const accum of values) {
      const statusValue: ClientStatusValue = {
        clientId: key,
        totalRequests: accum.totalRequests,
        limitedEndpoints: accum.limitedEndpoints
      };
      result.push([key, statusValue]);
    }
    return result;
  }
}

export class RequestCountReducer implements Reducer<RequestEventValue, RequestCountAccum> {
  initial: Nullable<RequestCountAccum> = null;

  constructor() {
  }

  add(accum: Nullable<RequestCountAccum>, value: RequestEventValue & DepSafe): RequestCountAccum {
    if (accum === null) {
      return {
        count: 1,
        latestTimestamp: value.timestamp
      };
    }
    return {
      count: accum.count + 1,
      latestTimestamp: value.timestamp > accum.latestTimestamp ? value.timestamp : accum.latestTimestamp
    };
  }

  remove(accum: RequestCountAccum, value: RequestEventValue & DepSafe): Nullable<RequestCountAccum> {
    const newCount = accum.count - 1;
    if (newCount <= 0) {
      return null;
    }
    if (value.timestamp >= accum.latestTimestamp) {
      return null;
    }
    return {
      count: newCount,
      latestTimestamp: accum.latestTimestamp
    };
  }
}

export class ClientAggregateReducer implements Reducer<ClientAggregateInput, ClientAggregateAccum> {
  initial: Nullable<ClientAggregateAccum> = null;

  constructor() {
  }

  add(accum: Nullable<ClientAggregateAccum>, value: ClientAggregateInput & DepSafe): ClientAggregateAccum {
    if (accum === null) {
      return {
        totalRequests: value.requestCount,
        limitedEndpoints: value.isLimited
      };
    }
    return {
      totalRequests: accum.totalRequests + value.requestCount,
      limitedEndpoints: accum.limitedEndpoints + value.isLimited
    };
  }

  remove(accum: ClientAggregateAccum, value: ClientAggregateInput & DepSafe): Nullable<ClientAggregateAccum> {
    const newTotal = accum.totalRequests - value.requestCount;
    const newLimited = accum.limitedEndpoints - value.isLimited;
    if (newTotal <= 0 && newLimited <= 0) {
      return null;
    }
    return {
      totalRequests: newTotal > 0 ? newTotal : 0,
      limitedEndpoints: newLimited > 0 ? newLimited : 0
    };
  }
}

export class RateLimitStatusResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RateLimitStatusId, RateLimitStatusValue> {
    return cs.rateLimitStatus;
  }
}

export class ClientStatusResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ClientStatusId, ClientStatusValue> {
    return cs.clientStatus;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
            this.inputs = { rateLimitConfigs: new InputDefinition<RateLimitConfigId, RateLimitConfigValue>([]), requestEvents: new InputDefinition<RequestEventId, RequestEventValue>([]) };
    this.resources = { "rateLimitStatus": RateLimitStatusResource, "clientStatus": ClientStatusResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const requestsByClientEndpoint = inputs.requestEvents
      .map(RequestEventToClientEndpointMapper);
    
    const requestCounts = requestsByClientEndpoint
      .reduce(RequestCountReducer);
    
    const rateLimitStatus = requestCounts
      .map(RequestCountToRateLimitStatusMapper, inputs.rateLimitConfigs);
    
    const clientAggregates = rateLimitStatus
      .map(RateLimitStatusToClientMapper)
      .reduce(ClientAggregateReducer);
    
    const clientStatus = clientAggregates
      .map(ClientAggregateToStatusMapper);
    
    return {
      rateLimitConfigs: inputs.rateLimitConfigs,
      requestEvents: inputs.requestEvents,
      rateLimitStatus: rateLimitStatus,
      clientStatus: clientStatus
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
