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
  console.log("Testing chat-room-service...\n");

  // Add users
  console.log("1. Adding users...");
  const users: InputEntries["users"] = [
    ["user1", [{ username: "alice", displayName: "Alice", lastSeen: Date.now() }]],
    ["user2", [{ username: "bob", displayName: "Bob", lastSeen: null }]],
  ];
  await broker.update("users", users);
  console.log("   Added 2 users");

  // Add rooms
  console.log("\n2. Adding rooms...");
  const rooms: InputEntries["rooms"] = [
    ["room1", [{ name: "General", createdAt: Date.now(), createdBy: "user1" }]],
    ["room2", [{ name: "Random", createdAt: Date.now(), createdBy: "user2" }]],
  ];
  await broker.update("rooms", rooms);
  console.log("   Added 2 rooms");

  // Add room members
  console.log("\n3. Adding room members...");
  const roomMembers: InputEntries["roomMembers"] = [
    ["member1", [{ roomId: "room1", userId: "user1", joinedAt: Date.now() }]],
    ["member2", [{ roomId: "room1", userId: "user2", joinedAt: Date.now() }]],
    ["member3", [{ roomId: "room2", userId: "user1", joinedAt: Date.now() }]],
  ];
  await broker.update("roomMembers", roomMembers);
  console.log("   Added 3 room members");

  // Add messages
  console.log("\n4. Adding messages...");
  const messages: InputEntries["messages"] = [
    ["msg1", [{ roomId: "room1", authorId: "user1", content: "Hello everyone!", timestamp: Date.now() }]],
    ["msg2", [{ roomId: "room1", authorId: "user2", content: "Hi Alice!", timestamp: Date.now() }]],
    ["msg3", [{ roomId: "room2", authorId: "user1", content: "Anyone here?", timestamp: Date.now() }]],
  ];
  await broker.update("messages", messages);
  console.log("   Added 3 messages");

  // Read all rooms
  console.log("\n5. Reading all rooms...");
  const allRoomsParams: ResourceParams["rooms"] = {};
  const allRooms = await broker.getAll("rooms", allRoomsParams);
  console.log("   Rooms:", JSON.stringify(allRooms, null, 2));

  // Read messages for room1 using parameterized resource
  console.log("\n6. Reading messages for room1 (parameterized resource)...");
  const room1Params: ResourceParams["rooms-messages"] = { roomId: "room1" };
  const room1Messages = await broker.getAll("rooms-messages", room1Params);
  console.log("   Room1 messages:", JSON.stringify(room1Messages, null, 2));

  // Read messages for room2
  console.log("\n7. Reading messages for room2...");
  const room2Params: ResourceParams["rooms-messages"] = { roomId: "room2" };
  const room2Messages = await broker.getAll("rooms-messages", room2Params);
  console.log("   Room2 messages:", JSON.stringify(room2Messages, null, 2));

  // Read members for room1
  console.log("\n8. Reading members for room1...");
  const membersParams: ResourceParams["rooms-members"] = { roomId: "room1" };
  const room1Members = await broker.getAll("rooms-members", membersParams);
  console.log("   Room1 members:", JSON.stringify(room1Members, null, 2));

  console.log("\nTest completed successfully!");
}

test().catch((err: unknown) => {
  console.error("Test failed:", err);
  process.exit(1);
});
