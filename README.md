# "Build Your Own Build your own Interpreter" CodeCrafters Challenge
This repository contains Rust solutions to the
["Build Your Own Build your own Interpreter" Challenge][challenge].

This challenge follows the book [Crafting Interpreters][book] by Robert
Nystrom.

In this challenge one builds a lexer, recursive-descent parser, and
AST-walking interpreter for [Lox][lox], a simple dynamically-typed
scripting language.

[challenge]: https://app.codecrafters.io/courses/interpreter/overview
[book]: https://craftinginterpreters.com
[lox]: https://craftinginterpreters.com/the-lox-language.html

## Lox Example
```JavaScript
class Breakfast {

  init(meat, bread) {
    this.meat = meat;
    this.bread = bread;
  }

  cook() {
    print "Eggs a-fryin'!";
  }

  serve(who) {
    print "Enjoy your " + this.meat + " and " +
        this.bread + ", " + who + ".";
  }
}

class Brunch < Breakfast {

  init(meat, bread, drink) {
    super.init(meat, bread);
    this.drink = drink;
  }

  offerDrink() {
    print "How about a " + this.drink + "?";
  }
}

fun main() {
  var brunch = Brunch("ham", "English muffin", "Bloody Mary");
  brunch.offerDrink();
  brunch.cook();
  brunch.serve("Noble Reader");
}

main();
```

## Tests
One can either run all tests via `make` (i.e., the default goal) or
individually as:
 - `make test-tokenize` to test the lexer
 - `make test-parse` to test the parser
 - `make test-evaluate` to test expression evaluation
 - `make test-run` to test the interpretation of Lox programs
