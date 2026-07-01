import type { User_skip_id_, FollowByFollowerValue, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface FollowsByFollowerResourceInputs extends SharedCollections {
  readonly followsByFollower: EagerCollection<
    User_skip_id_,
    FollowByFollowerValue
  >;
}

export class FollowsByFollowerResource implements Resource<FollowsByFollowerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: FollowsByFollowerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, FollowByFollowerValue> {
    return inputs.followsByFollower;
  }
}
