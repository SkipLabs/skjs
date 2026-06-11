function dayName(day: number): string {
  let name = "unknown";
  switch (day) {
    case 0:
      name = "sunday";
      break;
    case 6:
      name = "saturday";
      break;
    default:
      name = "weekday";
  }
  return name;
}
