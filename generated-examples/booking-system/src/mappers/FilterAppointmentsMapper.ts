import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  Appointment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each appointment entry, emit the entry unchanged when ALL of the following hold: (the customerId param is absent OR the entry's value's customerId field equals the customerId param) AND (the resourceId param is absent OR the entry's value's resourceId field equals the resourceId param) AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterAppointmentsMapper implements Mapper<
  Appointment_skip_id_,
  Appointment_skip_value_,
  Appointment_skip_id_,
  Appointment_skip_value_
> {
  constructor(
    private customerId: string | null,
    private resourceId: string | null,
    private status: string | null,
  ) {}

  mapEntry(
    key: Appointment_skip_id_,
    values: Values<Appointment_skip_value_>,
    context: Context,
  ): Iterable<[Appointment_skip_id_, Appointment_skip_value_]> {
    // > body
    const emits: [Appointment_skip_id_, Appointment_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.customerId !== null && value.customerId !== this.customerId)
        continue;
      if (this.resourceId !== null && value.resourceId !== this.resourceId)
        continue;
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
