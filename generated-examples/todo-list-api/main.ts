import { runService } from "./skipruntime/server.js";
import { service } from "./src/service.js";

console.log("Starting todo-list-api service...");
runService(service(), {
  streaming_port: 8080,
  control_port: 8081,
}).then(() => {
  console.log("Service running on ports 8080 (streaming) and 8081 (control)");
  console.log("Press Ctrl+C to stop");
}).catch((err: unknown) => {
  console.error("Failed to start service:", err);
  process.exit(1);
});
