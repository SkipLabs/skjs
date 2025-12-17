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

type Inputs = {
  urls: Entry<UrlId, UrlValue>[];
  clicks: Entry<ClickId, ClickValue>[];
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

type Resources = {
  "urls": new (params: Json) => Resource<GraphCollections>;
  "stats": new (params: Json) => Resource<GraphCollections>;
};

export class ClickToUrlKeyMapper implements Mapper<ClickId, ClickValue, UrlId, ClickForAggregation> {
  constructor() {
  }

  mapEntry(
    _key: ClickId,
    values: Values<ClickValue>,
    _context: Context
  ): Iterable<[UrlId, ClickForAggregation]> {
    const arr = values.toArray();
    const result: Array<[UrlId, ClickForAggregation]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const click = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[UrlStatsId, UrlStatsValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const stats = arr[i]!;
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
    const newLastClickAt = accum.lastClickAt === null 
      ? value.timestamp 
      : (value.timestamp > accum.lastClickAt ? value.timestamp : accum.lastClickAt);
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
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UrlId, UrlValue> {
    return cs.urls;
  }
}

export class StatsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UrlStatsId, UrlStatsValue> {
    return cs.clickStatsByUrl.map(StatsOutputMapper);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyUrls: Entry<UrlId, UrlValue>[] = Array.of();
    const emptyClicks: Entry<ClickId, ClickValue>[] = Array.of();
    this.initialData = { urls: emptyUrls, clicks: emptyClicks };
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
