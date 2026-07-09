import { WidgetByDashboardMapper } from "../mappers/WidgetByDashboardMapper.js";
import type {
  Widget_skip_id_,
  Widget_skip_value_,
  Dashboard_skip_id_,
  Widget,
  Dashboard,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface WidgetsByDashboardResourceInputs extends SharedCollections {
  readonly widgets: EagerCollection<Widget_skip_id_, Widget_skip_value_>;
}

export class WidgetsByDashboardResource implements Resource<WidgetsByDashboardResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: WidgetsByDashboardResourceInputs,
    _context: Context,
  ): EagerCollection<Dashboard_skip_id_, Widget> {
    const widgetsByDashboard = inputs.widgets.map(WidgetByDashboardMapper);
    return widgetsByDashboard;
  }
}
