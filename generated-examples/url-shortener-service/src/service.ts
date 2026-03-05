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
  UrlId,
  UrlValue,
  ClickId,
  ClickValue,
  UrlStatsId,
  UrlStatsValue,
} from "./types.js";

export type ClickForAggregation = {
  timestamp: number;
};

export type ClickStatsAccum = {
  totalClicks: number;
  lastClickAt: number | null;
};

export type Inputs = {
  urls: InputDefinition<UrlId, UrlValue>;
  clicks: InputDefinition<ClickId, ClickValue>;
};

export type InputCollections = {
  urls: EagerCollection<UrlId, UrlValue>;
  clicks: EagerCollection<ClickId, ClickValue>;
};

export type GraphCollections = {
  urls: EagerCollection<UrlId, UrlValue>;
  clicks: EagerCollection<ClickId, ClickValue>;
  clickStatsByUrl: EagerCollection<UrlId, ClickStatsAccum>;
};

export type Resources = {
  readonly "urls": ResourceClass<GraphCollections, {}>;
  readonly "stats": ResourceClass<GraphCollections, {}>;
};

export class ClickToUrlKeyMapper implements Mapper<ClickId, ClickValue, UrlId, ClickForAggregation> {
  constructor() {
  }

  mapEntry(
    _key: ClickId,
    values: Values<ClickValue>,
    _context: Context
  ): Iterable<[UrlId, ClickForAggregation]> {
    const result: Array<[UrlId, ClickForAggregation]> = Array.of();
    for (const click of values) {
      result.push([click.urlId, { timestamp: click.timestamp }]);
    }
    return result;
  }
}

export class StatsOutputMapper implements Mapper<UrlId, ClickStatsAccum, UrlStatsId, UrlStatsValue> {
  constructor() {
  }

  mapEntry(
    key: UrlId,
    values: Values<ClickStatsAccum>,
    _context: Context
  ): Iterable<[UrlStatsId, UrlStatsValue]> {
    const result: Array<[UrlStatsId, UrlStatsValue]> = Array.of();
    for (const stats of values) {
      const urlStatsId: UrlStatsId = key;
      const urlStatsValue: UrlStatsValue = {
        totalClicks: stats.totalClicks,
        lastClickAt: stats.lastClickAt
      };
      result.push([urlStatsId, urlStatsValue]);
    }
    return result;
  }
}

export class ClickStatsReducer implements Reducer<ClickForAggregation, ClickStatsAccum> {
  initial: Nullable<ClickStatsAccum> = null;

  constructor() {
  }

  add(accum: Nullable<ClickStatsAccum>, value: ClickForAggregation & DepSafe): ClickStatsAccum {
    if (accum === null) {
      return {
        totalClicks: 1,
        lastClickAt: value.timestamp
      };
    }
    const lastClickAt = accum.lastClickAt;
    const newLastClickAt = lastClickAt === null
      ? value.timestamp
      : (value.timestamp > lastClickAt ? value.timestamp : lastClickAt);
    return {
      totalClicks: accum.totalClicks + 1,
      lastClickAt: newLastClickAt
    };
  }

  remove(accum: ClickStatsAccum, _value: ClickForAggregation & DepSafe): Nullable<ClickStatsAccum> {
    if (accum.totalClicks <= 1) {
      return null;
    }
    return null;
  }
}

export class UrlsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UrlId, UrlValue> {
    return cs.urls;
  }
}

export class StatsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UrlStatsId, UrlStatsValue> {
    return cs.clickStatsByUrl.map(StatsOutputMapper);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
            this.inputs = { urls: new InputDefinition<UrlId, UrlValue>([]), clicks: new InputDefinition<ClickId, ClickValue>([]) };
    this.resources = { "urls": UrlsResource, "stats": StatsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const clicksByUrl = inputs.clicks.map(ClickToUrlKeyMapper);
    const clickStatsByUrl = clicksByUrl.reduce(ClickStatsReducer);
    
    return { 
      urls: inputs.urls, 
      clicks: inputs.clicks, 
      clickStatsByUrl: clickStatsByUrl 
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
