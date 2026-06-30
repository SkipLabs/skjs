import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Channel_skip_id_,
  Channel_skip_value_,
  Workspace_skip_id_,
  Channel,
  Workspace,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each channel entry, emit one output pair whose key is sourced from the entry's value's workspaceId field (which is the Workspace primary key), paired with a new value listing every required field of Channel explicitly: id is sourced from the entry's key, workspaceId is sourced from the entry's value's workspaceId field, name is sourced from the entry's value's name field, topic is sourced from the entry's value's topic field, createdById is sourced from the entry's value's createdById field, createdAt is sourced from the entry's value's createdAt field, updatedAt is sourced from the entry's value's updatedAt field.
export class ChannelsByWorkspaceMapper implements Mapper<
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
        ...(value.topic !== undefined && { topic: value.topic }),
        createdById: value.createdById,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
      };
      emits.push([value.workspaceId, channel]);
    }
    return emits;
    // < body
  }
}
