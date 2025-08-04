import { array } from "./skjs.js";

// program to shuffle the deck of cards

function main(): void {

  // declare card elements
  const suits = array("Spades", "Diamonds", "Club", "Heart");
  const values = array(
    "Ace",
    "2",
    "3",
    "4",
    "5",
    "6",
    "7",
    "8",
    "9",
    "10",
    "Jack",
    "Queen",
    "King",
  );

  // empty array to contain cards
  let deck = array();

  // create a deck of cards
  for (let i = 0; i < suits.length; i++) {
    for (let x = 0; x < values.length; x++) {
      const value = values[x];
      const suit = suits[i];
      if (value !== undefined && suit !== undefined) {
        let card = { Value: value, Suit: suit };
        deck.push(card);
      }
    }
  }

  // shuffle the cards
  for (let i = deck.length - 1; i > 0; i--) {
    let j = Math.floor(Math.random() * i);
    let temp = deck[i];
    deck[i] = deck[j];
    deck[j] = temp;
  }

  console.log('The first five cards are:');

  // display 5 results
  for (let i = 0; i < 5; i++) {
    const card = deck[i];
    if (card !== undefined) {
      console.log(card.Value + " of " + card.Suit);
    }
  }
}

main();
