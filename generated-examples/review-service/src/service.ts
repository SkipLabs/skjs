import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetReviewForSubjectResource } from "./resources/GetReviewForSubjectResource.js";
import { GetSubjectRatingSummaryResource } from "./resources/GetSubjectRatingSummaryResource.js";
import { ListMyReviewsResource } from "./resources/ListMyReviewsResource.js";
import { ListReviewsBySubjectInternalResource } from "./resources/ListReviewsBySubjectInternalResource.js";
import { ListReviewsForSubjectResource } from "./resources/ListReviewsForSubjectResource.js";
import { ListSubjectsResource } from "./resources/ListSubjectsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ReviewKey,
  ReviewStored,
  Subject_skip_id_,
  Subject_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListMyReviewsParams,
  ListReviewsForSubjectParams,
  Subject,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly reviews: InputDefinition<ReviewKey, ReviewStored>;
  readonly subjects: InputDefinition<Subject_skip_id_, Subject_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getReviewForSubjectResource: ResourceClass<GraphCollections, Json>;
  readonly getSubjectRatingSummaryResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listMyReviewsResource: ResourceClass<
    GraphCollections,
    ListMyReviewsParams
  >;
  readonly listReviewsBySubjectInternalResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listReviewsForSubjectResource: ResourceClass<
    GraphCollections,
    ListReviewsForSubjectParams
  >;
  readonly listSubjectsResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      reviews: new InputDefinition<ReviewKey, ReviewStored>([]),
      subjects: new InputDefinition<Subject_skip_id_, Subject_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getReviewForSubjectResource: GetReviewForSubjectResource,
      getSubjectRatingSummaryResource: GetSubjectRatingSummaryResource,
      listMyReviewsResource: ListMyReviewsResource,
      listReviewsBySubjectInternalResource:
        ListReviewsBySubjectInternalResource,
      listReviewsForSubjectResource: ListReviewsForSubjectResource,
      listSubjectsResource: ListSubjectsResource,
      getMeResource: getMeResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
