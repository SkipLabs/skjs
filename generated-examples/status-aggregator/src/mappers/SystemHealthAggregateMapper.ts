import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ComponentStored, SystemHealthAggregate } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// Receives ALL component values under the literal-zero key. Emit one output pair under the literal-zero key whose value is a SystemHealthAggregate record built by iterating over all received component values: componentCount is the total count of received values; healthyCount is the count of received values whose status field equals the literal 'HEALTHY'; degradedCount is the count of received values whose status field equals the literal 'DEGRADED'; unhealthyCount is the count of received values whose status field equals the literal 'UNHEALTHY'; unknownCount is the count of received values whose status field equals the literal 'UNKNOWN'; criticalUnhealthyCount is the count of received values whose criticality field equals the literal 'CRITICAL' AND whose status field equals the literal 'UNHEALTHY'. On an empty source, the output is empty by reactive construction — the consumer api method handles the zero-default (overallStatus 'UNKNOWN', all counts zero).
export class SystemHealthAggregateMapper implements Mapper<
  0,
  ComponentStored,
  0,
  SystemHealthAggregate
> {
  mapEntry(
    key: 0,
    values: Values<ComponentStored>,
    context: Context,
  ): Iterable<[0, SystemHealthAggregate]> {
    // > body
    let componentCount = 0;
    let healthyCount = 0;
    let degradedCount = 0;
    let unhealthyCount = 0;
    let unknownCount = 0;
    let criticalUnhealthyCount = 0;
    for (const value of values.toArray()) {
      componentCount++;
      if (value.status === "HEALTHY") healthyCount++;
      else if (value.status === "DEGRADED") degradedCount++;
      else if (value.status === "UNHEALTHY") unhealthyCount++;
      else if (value.status === "UNKNOWN") unknownCount++;
      if (value.criticality === "CRITICAL" && value.status === "UNHEALTHY")
        criticalUnhealthyCount++;
    }
    const aggregate: SystemHealthAggregate = {
      componentCount,
      healthyCount,
      degradedCount,
      unhealthyCount,
      unknownCount,
      criticalUnhealthyCount,
    };
    return [[0, aggregate]];
    // < body
  }
}
