import { ChannelsByWorkspaceMapper } from "../mappers/ChannelsByWorkspaceMapper.js";
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
} from "@skipruntime/core";

export interface ChannelsByWorkspaceResourceInputs extends SharedCollections {
  readonly channels: EagerCollection<Channel_skip_id_, Channel_skip_value_>;
}

export class ChannelsByWorkspaceResource implements Resource<ChannelsByWorkspaceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ChannelsByWorkspaceResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Channel> {
    const channelsByWorkspace = inputs.channels.map(ChannelsByWorkspaceMapper);
    return channelsByWorkspace;
  }
}
