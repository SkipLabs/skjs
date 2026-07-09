import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  User_skip_id_,
  Appointment,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each appointment entry, emit one output pair whose key is sourced from the entry's value providerId field, paired with a new value listing every required field of Appointment explicitly: id sourced from the entry's key; serviceId sourced from the entry's value serviceId field; customerId sourced from the entry's value customerId field; providerId sourced from the entry's value providerId field; startAt sourced from the entry's value startAt field; endAt sourced from the entry's value endAt field; status sourced from the entry's value status field; notes sourced from the entry's value notes field; revision sourced from the entry's value revision field; cancelledAt sourced from the entry's value cancelledAt field; cancelledBy sourced from the entry's value cancelledBy field; cancellationReason sourced from the entry's value cancellationReason field; completedAt sourced from the entry's value completedAt field; createdAt sourced from the entry's value createdAt field; updatedAt sourced from the entry's value updatedAt field.
export class AppointmentByProviderMapper implements Mapper<
  Appointment_skip_id_,
  Appointment_skip_value_,
  User_skip_id_,
  Appointment
> {
  mapEntry(
    key: Appointment_skip_id_,
    values: Values<Appointment_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Appointment]> {
    // > body
    const emits: [User_skip_id_, Appointment][] = [];
    for (const value of values.toArray()) {
      const appointment: Appointment = {
        id: key,
        serviceId: value.serviceId,
        customerId: value.customerId,
        providerId: value.providerId,
        startAt: value.startAt,
        endAt: value.endAt,
        status: value.status,
        revision: value.revision,
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
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.providerId, appointment]);
    }
    return emits;
    // < body
  }
}
