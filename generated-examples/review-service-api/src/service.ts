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
  ReviewId,
  ReviewValue,
  ReviewsByItemResourceParams,
  ReviewsByUserResourceParams,
} from "./types.js";


export type Inputs = {
  reviews: InputDefinition<ReviewId, ReviewValue>;
};

export type InputCollections = {
  reviews: EagerCollection<ReviewId, ReviewValue>;
};

export type GraphCollections = {
  reviews: EagerCollection<ReviewId, ReviewValue>;
};

export type Resources = {
  readonly "reviews-by-item": ResourceClass<GraphCollections, ReviewsByItemResourceParams>;
  readonly "reviews-by-user": ResourceClass<GraphCollections, ReviewsByUserResourceParams>;
};

export class FilterByItemMapper implements Mapper<ReviewId, ReviewValue, ReviewId, ReviewValue> {
  private itemId: string;

  constructor(itemId: string) {
    this.itemId = itemId;
  }

  mapEntry(
    key: ReviewId,
    values: Values<ReviewValue>,
    _context: Context
  ): Iterable<[ReviewId, ReviewValue]> {
    const result: Array<[ReviewId, ReviewValue]> = Array.of();
    for (const v of values) {
      if (v.itemId === this.itemId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class FilterByUserMapper implements Mapper<ReviewId, ReviewValue, ReviewId, ReviewValue> {
  private userId: string;

  constructor(userId: string) {
    this.userId = userId;
  }

  mapEntry(
    key: ReviewId,
    values: Values<ReviewValue>,
    _context: Context
  ): Iterable<[ReviewId, ReviewValue]> {
    const result: Array<[ReviewId, ReviewValue]> = Array.of();
    for (const v of values) {
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class ReviewsByItemResource implements Resource<GraphCollections> {
  private itemId: string;

  constructor(params: ReviewsByItemResourceParams) {
    this.itemId = params.itemId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReviewId, ReviewValue> {
    return cs.reviews.map(FilterByItemMapper, this.itemId);
  }
}

export class ReviewsByUserResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: ReviewsByUserResourceParams) {
    this.userId = params.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReviewId, ReviewValue> {
    return cs.reviews.map(FilterByUserMapper, this.userId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
        this.inputs = { reviews: new InputDefinition<ReviewId, ReviewValue>([]) };
    this.resources = { "reviews-by-item": ReviewsByItemResource, "reviews-by-user": ReviewsByUserResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { reviews: inputs.reviews };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections> {
  return new Service();
}
