import { FilterAvailabilityByResourceMapper } from "../mappers/FilterAvailabilityByResourceMapper.js";
import type {
  AvailabilityWindowKey,
  AvailabilityWindowStored,
  ListAvailabilityParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListAvailabilityWindowsResourceInputs extends SharedCollections {
  readonly availabilityWindows: EagerCollection<
    AvailabilityWindowKey,
    AvailabilityWindowStored
  >;
}

export class ListAvailabilityWindowsResource implements Resource<ListAvailabilityWindowsResourceInputs> {
  private readonly resourceId: string;

  constructor(params: ListAvailabilityParams) {
    this.resourceId = params.resourceId;
  }

  instantiate(
    inputs: ListAvailabilityWindowsResourceInputs,
    _context: Context,
  ): EagerCollection<AvailabilityWindowKey, AvailabilityWindowStored> {
    return inputs.availabilityWindows.map(
      FilterAvailabilityByResourceMapper,
      this.resourceId,
    );
  }
}
