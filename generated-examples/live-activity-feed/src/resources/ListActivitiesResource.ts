import { ActivityByCreatedAtMapper } from "../mappers/ActivityByCreatedAtMapper.js";
import { FilterActivityMapper } from "../mappers/FilterActivityMapper.js";
import type {
  Activity_skip_id_,
  Activity_skip_value_,
  ActivityCreatedAtKey,
  Activity,
  ListActivitiesParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListActivitiesResourceInputs extends SharedCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
}

export class ListActivitiesResource implements Resource<ListActivitiesResourceInputs> {
  private readonly authorId: string | null;
  private readonly type: string | null;

  constructor(params: ListActivitiesParams) {
    this.authorId = params.authorId ?? null;
    this.type = params.type ?? null;
  }

  instantiate(
    inputs: ListActivitiesResourceInputs,
    _context: Context,
  ): EagerCollection<ActivityCreatedAtKey, Activity> {
    const activitiesByCreatedAt = inputs.activities.map(
      ActivityByCreatedAtMapper,
    );
    return activitiesByCreatedAt.map(
      FilterActivityMapper,
      this.authorId,
      this.type,
    );
  }
}
