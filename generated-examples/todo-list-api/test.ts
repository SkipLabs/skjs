import { SkipServiceBroker } from "@skipruntime/helpers";
import type { Entry, InputDefinition, ResourceClass } from "./skipruntime/core.js";
import type { Inputs, Resources } from "./src/service.js";

// Derive entry types from the service's Inputs type
type InputEntries = {
  [K in keyof Inputs]: Inputs[K] extends InputDefinition<infer Key, infer Val>
    ? Entry<Key, Val>[]
    : never;
};

// Derive resource param types from the service's Resources type
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type ResourceParams = {
  [K in keyof Resources]: Resources[K] extends ResourceClass<any, infer Params>
    ? Params
    : never;
};

const broker = new SkipServiceBroker({
  host: "localhost",
  streaming_port: 8080,
  control_port: 8081,
});

async function test() {
  console.log("Testing todo-list-api service...\n");

  // Add some todos
  console.log("1. Adding todos...");
  const now = Date.now();
  const todos: InputEntries["todos"] = [
    ["1", [{ title: "Learn Skip", completed: 0, description: null, dueDate: null, createdAt: now }]],
    ["2", [{ title: "Build reactive service", completed: 0, description: "Build a reactive Skip service", dueDate: null, createdAt: now }]],
    ["3", [{ title: "Write tests", completed: 1, description: null, dueDate: null, createdAt: now }]],
  ];
  await broker.update("todos", todos);
  console.log("   Added 3 todos");

  // Read all todos
  console.log("\n2. Reading all todos...");
  const allTodosParams: ResourceParams["todos"] = {};
  const allTodos = await broker.getAll("todos", allTodosParams);
  console.log("   All todos:", JSON.stringify(allTodos, null, 2));

  // Read a specific todo
  console.log("\n3. Reading todo with id=2...");
  const todo2 = await broker.getUnique("todos", {}, "2");
  console.log("   Todo 2:", JSON.stringify(todo2, null, 2));

  console.log("\nTest completed successfully!");
}

test().catch((err: unknown) => {
  console.error("Test failed:", err);
  process.exit(1);
});
