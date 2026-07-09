import { ChannelByWorkspaceMapper } from "../mappers/ChannelByWorkspaceMapper.js";
import type {
  Channel_skip_id_,
  Channel_skip_value_,
  Workspace_skip_id_,
  Channel,
  Workspace,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListWorkspaceChannelsResourceInputs extends SharedCollections {
  readonly channels: EagerCollection<Channel_skip_id_, Channel_skip_value_>;
}

export class ListWorkspaceChannelsResource implements Resource<ListWorkspaceChannelsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListWorkspaceChannelsResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Channel> {
    const channelsByWorkspace = inputs.channels.map(ChannelByWorkspaceMapper);
    return channelsByWorkspace;
  }
}
