import { array } from "./skjs.js";

// program to remove duplicate value from an array

function getUnique<T>(arr: Array<T>): Array<T> {
  
  let uniqueArr = array();
  
  // loop through array
  for(let i = 0; i < arr.length; i++) {
    const item = arr[i];
    if(item !== undefined && uniqueArr.indexOf(item) === -1) {
      uniqueArr.push(item);
    }
  }
  return uniqueArr;
}

// calling the function
// passing array argument
console.log(getUnique(array(1, 2, 3, 2, 3)));
