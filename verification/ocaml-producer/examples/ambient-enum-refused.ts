// An ambient enum: its object is the environment's, and the declaration
// reader has no ambient enum value.
declare enum Level {
  Low = 0,
  High = 1,
}
export function low(): Level {
  return Level.Low;
}
