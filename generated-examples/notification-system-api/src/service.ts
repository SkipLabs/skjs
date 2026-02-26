import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  NotificationId,
  NotificationValue,
  NotificationsUserResourceParams,
} from "./types.js";


export type Inputs = {
  notifications: InputDefinition<NotificationId, NotificationValue>;
};

export type InputCollections = {
  notifications: EagerCollection<NotificationId, NotificationValue>;
};

export type GraphCollections = {
  notifications: EagerCollection<NotificationId, NotificationValue>;
};

export type Resources = {
  "notifications": ResourceClass<GraphCollections, {}>;
  "notifications-unread": ResourceClass<GraphCollections, {}>;
  "notifications-user": ResourceClass<GraphCollections, NotificationsUserResourceParams>;
};

export class UnreadNotificationsMapper implements Mapper<NotificationId, NotificationValue, NotificationId, NotificationValue> {
  constructor() {
  }

  mapEntry(
    key: NotificationId,
    values: Values<NotificationValue>,
    _context: Context
  ): Iterable<[NotificationId, NotificationValue]> {
    const result: Array<[NotificationId, NotificationValue]> = Array.of();
    for (const v of values) {
      if (v.read === 0) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class NotificationsByUserMapper implements Mapper<NotificationId, NotificationValue, NotificationId, NotificationValue> {
  private userId: string;

  constructor(userId: string) {
    this.userId = userId;
  }

  mapEntry(
    key: NotificationId,
    values: Values<NotificationValue>,
    _context: Context
  ): Iterable<[NotificationId, NotificationValue]> {
    const result: Array<[NotificationId, NotificationValue]> = Array.of();
    for (const v of values) {
      if (v.userId === this.userId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class NotificationsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications;
  }
}

export class NotificationsUnreadResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications.map(UnreadNotificationsMapper);
  }
}

export class NotificationsUserResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: NotificationsUserResourceParams) {
    this.userId = params.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<NotificationId, NotificationValue> {
    return cs.notifications.map(NotificationsByUserMapper, this.userId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
        this.inputs = { notifications: new InputDefinition<NotificationId, NotificationValue>([]) };
    this.resources = { "notifications": NotificationsResource, "notifications-unread": NotificationsUnreadResource, "notifications-user": NotificationsUserResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { notifications: inputs.notifications };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
