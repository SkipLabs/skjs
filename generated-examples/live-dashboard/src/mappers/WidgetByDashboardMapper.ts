import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Widget_skip_id_,
  Widget_skip_value_,
  Dashboard_skip_id_,
  Widget,
  Dashboard,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each widget entry, emit one output pair whose key is sourced from the entry's value's dashboardId field (a Dashboard id) and whose value is a Widget record listing every required field explicitly: id sourced from the entry's key; dashboardId sourced from the entry's value's dashboardId field; metricId sourced from the entry's value's metricId field; title sourced from the entry's value's title field; chartType sourced from the entry's value's chartType field; positionX sourced from the entry's value's positionX field; positionY sourced from the entry's value's positionY field; width sourced from the entry's value's width field; height sourced from the entry's value's height field; createdAt sourced from the entry's value's createdAt field; updatedAt sourced from the entry's value's updatedAt field.
export class WidgetByDashboardMapper implements Mapper<
  Widget_skip_id_,
  Widget_skip_value_,
  Dashboard_skip_id_,
  Widget
> {
  mapEntry(
    key: Widget_skip_id_,
    values: Values<Widget_skip_value_>,
    context: Context,
  ): Iterable<[Dashboard_skip_id_, Widget]> {
    // > body
    const emits: [Dashboard_skip_id_, Widget][] = [];
    for (const value of values.toArray()) {
      const widget: Widget = {
        id: key,
        dashboardId: value.dashboardId,
        metricId: value.metricId,
        title: value.title,
        chartType: value.chartType,
        positionX: value.positionX,
        positionY: value.positionY,
        width: value.width,
        height: value.height,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
      };
      emits.push([value.dashboardId, widget]);
    }
    return emits;
    // < body
  }
}
