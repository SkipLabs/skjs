import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  BookableResource_skip_id_,
  Appointment,
  BookableResource,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each appointment entry, emit one output pair whose key is sourced from the entry's value's resourceId field, paired with a new value listing every required field of Appointment explicitly — id sourced from the entry's key; customerId sourced from the entry's value's customerId field; resourceId sourced from the entry's value's resourceId field; startsAt sourced from the entry's value's startsAt field; endsAt sourced from the entry's value's endsAt field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field; and every optional field with an explicit presence clause: notes present when the entry's value carries a notes field, sourced from the entry's value's notes field, absent otherwise; cancelledAt present when the entry's value carries a cancelledAt field, sourced from the entry's value's cancelledAt field, absent otherwise; cancelledBy present when the entry's value carries a cancelledBy field, sourced from the entry's value's cancelledBy field, absent otherwise; cancellationReason present when the entry's value carries a cancellationReason field, sourced from the entry's value's cancellationReason field, absent otherwise; completedAt present when the entry's value carries a completedAt field, sourced from the entry's value's completedAt field, absent otherwise. The id is re-injected on the value side so the reschedule handler can exclude the appointment being rescheduled from the overlap set when consulting AppointmentsByResourceResource by resourceId.
export class AppointmentsByResourceMapper implements Mapper<
  Appointment_skip_id_,
  Appointment_skip_value_,
  BookableResource_skip_id_,
  Appointment
> {
  mapEntry(
    key: Appointment_skip_id_,
    values: Values<Appointment_skip_value_>,
    context: Context,
  ): Iterable<[BookableResource_skip_id_, Appointment]> {
    // > body
    const emits: [BookableResource_skip_id_, Appointment][] = [];
    for (const value of values.toArray()) {
      const appointment: Appointment = {
        id: key,
        customerId: value.customerId,
        resourceId: value.resourceId,
        startsAt: value.startsAt,
        endsAt: value.endsAt,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.notes !== undefined && { notes: value.notes }),
        ...(value.cancelledAt !== undefined && {
          cancelledAt: value.cancelledAt,
        }),
        ...(value.cancelledBy !== undefined && {
          cancelledBy: value.cancelledBy,
        }),
        ...(value.cancellationReason !== undefined && {
          cancellationReason: value.cancellationReason,
        }),
        ...(value.completedAt !== undefined && {
          completedAt: value.completedAt,
        }),
      };
      emits.push([value.resourceId, appointment]);
    }
    return emits;
    // < body
  }
}
