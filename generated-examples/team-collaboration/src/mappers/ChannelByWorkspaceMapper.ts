import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Channel_skip_id_,
  Channel_skip_value_,
  Workspace_skip_id_,
  Channel,
  Workspace,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each channel entry, emit a new key sourced from the entry's value's workspaceId field, paired with a new value that carries every required field of Channel explicitly — id sourced from the entry's key, workspaceId sourced from the entry's value's workspaceId field, name sourced from the entry's value's name field, createdBy sourced from the entry's value's createdBy field, createdAt sourced from the entry's value's createdAt field; topic is optional, present when the entry's value's topic field is present, sourced from the entry's value's topic field, absent otherwise; updatedAt is optional, present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field, absent otherwise.
export class ChannelByWorkspaceMapper implements Mapper<
  Channel_skip_id_,
  Channel_skip_value_,
  Workspace_skip_id_,
  Channel
> {
  mapEntry(
    key: Channel_skip_id_,
    values: Values<Channel_skip_value_>,
    context: Context,
  ): Iterable<[Workspace_skip_id_, Channel]> {
    // > body
    const emits: [Workspace_skip_id_, Channel][] = [];
    for (const value of values.toArray()) {
      const channel: Channel = {
        id: key,
        workspaceId: value.workspaceId,
        name: value.name,
        createdBy: value.createdBy,
        createdAt: value.createdAt,
        ...(value.topic !== undefined && { topic: value.topic }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.workspaceId, channel]);
    }
    return emits;
    // < body
  }
}
