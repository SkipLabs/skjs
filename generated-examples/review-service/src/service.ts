import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetReviewResource } from "./resources/GetReviewResource.js";
import { GetSubjectStoredResource } from "./resources/GetSubjectStoredResource.js";
import { ReviewsByAuthorResource } from "./resources/ReviewsByAuthorResource.js";
import { ReviewsByAuthorSubjectResource } from "./resources/ReviewsByAuthorSubjectResource.js";
import { ReviewsBySubjectResource } from "./resources/ReviewsBySubjectResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  Subject_skip_id_,
  SubjectStored,
  User_skip_id_,
  User_skip_value_,
  Review,
  Subject,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly reviews: InputDefinition<Review_skip_id_, Review_skip_value_>;
  readonly subjects: InputDefinition<Subject_skip_id_, SubjectStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getReviewResource: ResourceClass<GraphCollections, Json>;
  readonly getSubjectStoredResource: ResourceClass<GraphCollections, Json>;
  readonly reviewsByAuthorResource: ResourceClass<GraphCollections, Json>;
  readonly reviewsByAuthorSubjectResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly reviewsBySubjectResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      reviews: new InputDefinition<Review_skip_id_, Review_skip_value_>([]),
      subjects: new InputDefinition<Subject_skip_id_, SubjectStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getReviewResource: GetReviewResource,
      getSubjectStoredResource: GetSubjectStoredResource,
      reviewsByAuthorResource: ReviewsByAuthorResource,
      reviewsByAuthorSubjectResource: ReviewsByAuthorSubjectResource,
      reviewsBySubjectResource: ReviewsBySubjectResource,
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
