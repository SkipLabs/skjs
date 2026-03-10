// program to remove duplicate values from an array

function getUnique<T>(arr: Array<T>): Array<T> {
  let uniqueArr = [];

  // loop through array
  for (let i = 0; i < arr.length; i++) {
    const item = arr[i];
    if (item !== undefined && uniqueArr.indexOf(item) === -1) {
      uniqueArr.push(item);
    }
  }
  return uniqueArr;
}

// calling the function
// passing array argument
console.log(getUnique([1, 2, 3, 2, 3]));
