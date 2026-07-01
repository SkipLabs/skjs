import { FilterResourceByParentMapper } from "../mappers/FilterResourceByParentMapper.js";
import type {
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_,
  ListResourcesParams,
  ProtectedResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListResourcesResourceInputs extends SharedCollections {
  readonly resources: EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  >;
}

export class ListResourcesResource implements Resource<ListResourcesResourceInputs> {
  private readonly parentResourceId: string | null;

  constructor(params: ListResourcesParams) {
    this.parentResourceId = params.parentResourceId ?? null;
  }

  instantiate(
    inputs: ListResourcesResourceInputs,
    _context: Context,
  ): EagerCollection<
    ProtectedResource_skip_id_,
    ProtectedResource_skip_value_
  > {
    return inputs.resources.map(
      FilterResourceByParentMapper,
      this.parentResourceId,
    );
  }
}
