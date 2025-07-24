import { array } from "./skjs.js";

type node = {
  item: number,
  height: number,
  left: null | node,
  right: null | node,
};

type tree = {
  height: (n: node) => number,
  rightRotate: (n: node) => node,
  leftRotate: (n: node) => node,
};

function foo<T1 extends { fd1: number }, T2 extends  {fd2: number}>(
  v: T1,
  x: T1 & T2
): {fd1: number, fd2: number} {
  return x;
}
function foo2(x: Array<number>): Array<number> {
  return x;
}

// Create node
function Node(item: number): node {
  let obj = {};
  obj.item = item;
  obj.height = 1;
  obj.left = null;
  obj.right = null;
  return obj;
}

//return height of the node
function height(N: node | null): number {
  if (N === null){
    return 0;
  }
  
  return N.height;
}

  //right rotate
function rightRotate(y: node): node {
  let x = y.left;
  console.assert(x !== null);
  let T2 = x.right;
  x.right = y;
  y.left = T2;
  y.height = Math.max(height(y.left), height(y.right)) + 1;
  x.height = Math.max(height(x.left), height(x.right)) + 1;
  return x;
}

//left rotate
function leftRotate(x: node): node {
  let y = x.right;
  console.assert(y !== null);
  let T2 = y.left;
  y.left = x;
  x.right = T2;
  x.height = Math.max(height(x.left), height(x.right)) + 1;
  y.height = Math.max(height(y.left), height(y.right)) + 1;
  return y;
}


// get balance factor of a node
function getBalanceFactor(N: null | node): number {
  if (N === null){
    return 0;
  }
  
  return height(N.left) - height(N.right);
}

// helper function to insert a node
function insertNodeHelper(node: null | node, item: number): node {

  // find the position and insert the node
  if (node === null){
    return (Node(item));
  }
  
  if (item < node.item){
    node.left = insertNodeHelper(node.left, item);
  } else if (item > node.item){
    node.right = insertNodeHelper(node.right, item);
  } else{
    return node;
  }
  
  // update the balance factor of each node
  // and, balance the tree
  node.height = 1 + Math.max(height(node.left), height(node.right));
  
  let balanceFactor = getBalanceFactor(node);
  
  if (balanceFactor > 1) {
    let left = node.left;
    console.assert(left !== null);
    if (item < left.item) {
      return rightRotate(node);
    } else if (item > left.item) {
      node.left = leftRotate(left);
      return rightRotate(node);
    }
  }
  
  if (balanceFactor < -1) {
    let right = node.right;
    console.assert(right !== null);
    if (item > right.item) {
      return leftRotate(node);
    } else if (item < right.item) {
      node.right = rightRotate(right);
      return leftRotate(node);
    }
  }
  
  return node;
}

// delete helper
function deleteNodeHelper(root: null | node, item: number): null | node {

  // find the node to be deleted and remove it
  if (root === null){
    return root;
  }
  if (item < root.item){
    root.left = deleteNodeHelper(root.left, item);
  }else if (item > root.item){
    root.right = deleteNodeHelper(root.right, item);
  }else {
    let left = root.left;
    let right = root.right;
    if ((left === null) || (right === null)) {
      let temp = null;
      if (temp === left){
        temp = right;
      }else{
        temp = left;
      }
      
      if (temp === null) {
        temp = root;
        root = null;
      } else{
        root = temp;
      }
    } else {
      let temp = nodeWithMinimumValue(right);
      root.item = temp.item;
      root.right = deleteNodeHelper(root.right, temp.item);
    }
  }
  if (root === null){
    return root;
  }

  // Update the balance factor of each node and balance the tree
  root.height = Math.max(height(root.left), height(root.right)) + 1;
  
  let balanceFactor = getBalanceFactor(root);
  if (balanceFactor > 1) {
    if (getBalanceFactor(root.left) >= 0) {
      return rightRotate(root);
    } else {
      let left = root.left;
      console.assert(left !== null);
      root.left = leftRotate(left);
      return rightRotate(root);
    }
  }
  if (balanceFactor < -1) {
    if (getBalanceFactor(root.right) <= 0) {
      return leftRotate(root);
    } else {
      let right = root.right;
      console.assert(right !== null);
      root.right = rightRotate(right);
      return leftRotate(root);
    }
  }
  return root;
}


//get node with minimum value
function nodeWithMinimumValue(node: node): node {
  let current = node;
  while (current.left !== null){
    let left = current.left;
    console.assert(left !== null);
    current = left;
  }
  return current;
}

function preOrderHelper(node: null | node): void {
  if (node !== null) {
    console.log(node.item);
    preOrderHelper(node.left);
    preOrderHelper(node.right);
  }
}

//AVL Tree
function AVLTree(): void {
  let rroot = null;
  let obj = {};
          
  // insert a node
  obj.insertNode = (item: number) => {
    // console.log(root);
    rroot = insertNodeHelper(rroot, item);
  }
      
  //delete a node
  obj.deleteNode = (item: number) => {
    rroot = deleteNodeHelper(rroot, item);
  }
  
  // print the tree in pre - order
  obj.preOrder = () => {
    preOrderHelper(rroot);
  }

  for(let i = 0; i < 10; i++) {
    obj.insertNode(i);
  };
  console.log(rroot);
}

AVLTree()
