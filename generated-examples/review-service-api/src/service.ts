import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

import type {
  ReviewId,
  ReviewValue,
  ReviewsByItemResourceParams,
  ReviewsByUserResourceParams,
} from "./types.js";


type Inputs = {
  reviews: Entry<ReviewId, ReviewValue>[];
};

export type InputCollections = {
  reviews: EagerCollection<ReviewId, ReviewValue>;
};

export type GraphCollections = {
  reviews: EagerCollection<ReviewId, ReviewValue>;
};

type Resources = {
  "reviews-by-item": new (params: Json) => Resource<GraphCollections>;
  "reviews-by-user": new (params: Json) => Resource<GraphCollections>;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class ReviewsByItemResource implements Resource<GraphCollections> {
  private itemId: string;

  constructor(params: Json) {
    const typed = params as ReviewsByItemResourceParams;
    this.itemId = typed.itemId;
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

  constructor(params: Json) {
    const typed = params as ReviewsByUserResourceParams;
    this.userId = typed.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ReviewId, ReviewValue> {
    return cs.reviews.map(FilterByUserMapper, this.userId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyReviews: Entry<ReviewId, ReviewValue>[] = Array.of();
    this.initialData = { reviews: emptyReviews };
    this.resources = { "reviews-by-item": ReviewsByItemResource, "reviews-by-user": ReviewsByUserResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { reviews: inputs.reviews };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
