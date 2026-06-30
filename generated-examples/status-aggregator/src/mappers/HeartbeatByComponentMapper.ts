import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Heartbeat_skip_id_,
  Heartbeat_skip_value_,
  ComponentIdKey,
  Heartbeat,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each heartbeat entry, emit one output pair whose key is sourced from the entry's value's componentId field, paired with a new value listing every required field of Heartbeat explicitly: id sourced from the entry's key (= the original Heartbeat.id, preserved on the value side); componentId sourced from the entry's value's componentId field; status sourced from the entry's value's status field; receivedAt sourced from the entry's value's receivedAt field; reportedByUserId sourced from the entry's value's reportedByUserId field; message sourced from the entry's value's message field when present. The original Heartbeat.id is preserved on the value as the new value's id property; downstream consumers consult by componentId and recover each heartbeat's id directly from the emitted Heartbeat value.
export class HeartbeatByComponentMapper implements Mapper<
  Heartbeat_skip_id_,
  Heartbeat_skip_value_,
  ComponentIdKey,
  Heartbeat
> {
  mapEntry(
    key: Heartbeat_skip_id_,
    values: Values<Heartbeat_skip_value_>,
    context: Context,
  ): Iterable<[ComponentIdKey, Heartbeat]> {
    // > body
    const emits: [ComponentIdKey, Heartbeat][] = [];
    for (const value of values.toArray()) {
      const heartbeat: Heartbeat = {
        id: key,
        componentId: value.componentId,
        status: value.status,
        receivedAt: value.receivedAt,
        reportedByUserId: value.reportedByUserId,
        ...(value.message !== undefined && { message: value.message }),
      };
      emits.push([value.componentId, heartbeat]);
    }
    return emits;
    // < body
  }
}
