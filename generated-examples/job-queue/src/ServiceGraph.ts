import { RunningJobByQueueMapper } from "./mappers/RunningJobByQueueMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Job_skip_id_,
  Job,
  Job_skip_value_,
  Queue_skip_id_,
  Queue,
  Queue_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  RunningJobCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
  readonly queues: EagerCollection<Queue_skip_id_, Queue_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly jobs: EagerCollection<Job_skip_id_, Job_skip_value_>;
  readonly queues: EagerCollection<Queue_skip_id_, Queue_skip_value_>;
  readonly runningCountByQueue: EagerCollection<
    Queue_skip_id_,
    RunningJobCount
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_jobs = inputs.jobs;
  const output_queues = inputs.queues;
  const runningJobsByQueue = inputs.jobs.map(RunningJobByQueueMapper);
  const runningCountByQueue = runningJobsByQueue.reduce(SumReducer);
  const output_runningCountByQueue = runningCountByQueue;
  const output_users = inputs.users;
  return {
    jobs: output_jobs,
    queues: output_queues,
    runningCountByQueue: output_runningCountByQueue,
    users: output_users,
  };
}
