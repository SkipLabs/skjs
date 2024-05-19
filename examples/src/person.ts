// program to create JavaScript object using object literal
function main(): void {
  const person = { 
    name: 'John',
    age: 20,
    hobbies: ['reading', 'games', 'coding'],
    greet: () => {
      console.log('Hello everyone.');
    },
    score: {
      maths: 90,
      science: 80
    }
  };

  console.log(typeof person); // object

  // accessing the object value
  console.log(person.name);
  console.log(person.hobbies[0]);
  person.greet();
  console.log(person.score.maths);
}

main();
