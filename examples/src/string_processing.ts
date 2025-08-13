// String manipulation and processing

function isPalindrome(str: string): boolean {
    let cleaned: string = str.toLowerCase();
    let left: number = 0;
    let right: number = cleaned.length - 1;
    
    while (left < right) {
        if (cleaned.charAt(left) !== cleaned.charAt(right)) {
            return false;
        }
        left = left + 1;
        right = right - 1;
    }
    return true;
}

function countWords(text: string): number {
    if (text.length === 0) {
        return 0;
    }
    let words: Array<string> = text.split(" ");
    return words.length;
}

function capitalize(str: string): string {
    if (str.length === 0) {
        return str;
    }
    let first: string = str.charAt(0).toUpperCase();
    let rest: string = str.substring(1).toLowerCase();
    return first + rest;
}

function findLongestWord(text: string): string {
    let words: Array<string> = text.split(" ");
    if (words.length === 0) {
        return "";
    }
    
    let firstWord = words[0];
    if (firstWord === undefined) {
        return "";
    }
    let longest: string = firstWord;
    for (let i = 1; i < words.length; i++) {
        let current = words[i];
        if (current !== undefined && current.length > longest.length) {
            longest = current;
        }
    }
    return longest;
}

function removeVowels(str: string): string {
    let result: string = "";
    for (let i = 0; i < str.length; i++) {
        let char: string = str.charAt(i).toLowerCase();
        if (char !== "a" && char !== "e" && char !== "i" && char !== "o" && char !== "u") {
            result = result + str.charAt(i);
        }
    }
    return result;
}

function reverseWords(text: string): string {
    let words: Array<string> = text.split(" ");
    let result: string = "";
    
    for (let i = words.length - 1; i >= 0; i--) {
        let word = words[i];
        if (word !== undefined) {
            result = result + word;
            if (i > 0) {
                result = result + " ";
            }
        }
    }
    return result;
}

function stringProcessingDemo(): void {
    console.log("Is 'racecar' palindrome: " + isPalindrome("racecar").toString());
    console.log("Is 'hello' palindrome: " + isPalindrome("hello").toString());
    
    let text: string = "The quick brown fox jumps over the lazy dog";
    console.log("Word count: " + countWords(text).toString());
    console.log("Longest word: " + findLongestWord(text));
    
    console.log("Capitalize 'hello world': " + capitalize("hello world"));
    console.log("Remove vowels from 'hello': " + removeVowels("hello"));
    console.log("Reverse words: " + reverseWords("hello world"));
}

stringProcessingDemo();