import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetLinkResource } from "./resources/GetLinkResource.js";
import { LinkByCodeResource } from "./resources/LinkByCodeResource.js";
import { ListMyLinksResource } from "./resources/ListMyLinksResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListMyLinksParams,
  Link,
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
  readonly links: InputDefinition<Link_skip_id_, Link_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getLinkResource: ResourceClass<GraphCollections, Json>;
  readonly linkByCodeResource: ResourceClass<GraphCollections, Json>;
  readonly listMyLinksResource: ResourceClass<
    GraphCollections,
    ListMyLinksParams
  >;
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
      links: new InputDefinition<Link_skip_id_, Link_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getLinkResource: GetLinkResource,
      linkByCodeResource: LinkByCodeResource,
      listMyLinksResource: ListMyLinksResource,
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
