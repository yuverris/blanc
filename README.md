# blanc
yet another (WIP) programming language

## Example
```blanc
print("hello, world!");
```

## Data types
```blanc
1; // integer

3.14; // float

true;
false; // bool

"hello"; // string

'a'; // char

[1,2,3, true]; // array

{"hello": 5}; // map soon™

(12, "hello", false, "there"); // tuple soon™
```

## Variables
variables are declared with the `let` keyword

```blanc
let x = 1;
let y = 2;

let z = x + y;
print(x, '+', y, '=', z);

x = 3; // can also re-assign

let a = {
    return 3;
}; // can also use blocks, by default a null is returned unless if there is a return statement
```

## Functions
function definition starts with the `fnc` keyword, like
```blanc
fnc get_1() {
    return 1;
};
fnc get_2() {
    return 2;
};
print(get_1() + get_2());

// or

let get_1 = fnc() -> 1;
let get_2 = fnc() -> 2;
print(get_1() + get_2());

// or
(get_1() + get_2()).print();
```

blanc also supports keyword argumnets as `arg: value`
```blanc
fnc do_stuff(a, b, c) {
   print("a is", a, "b is", b, "c is", c);
};
do_stuff(b: 2, c: 3, a: 1); 
do_stuff(1, c: 3, 2); // can appear in any order in function call
do_stuff(c: 3, 1, 2);
do_stuff(1, 2, 3);
```

as well as default argumens
```blanc
fnc foo(a, b = 3) {
   return a + b; 
}
foo(1); // 4
foo(1, 2); // 3
```

## Control Flow
```blanc
fnc fact(x) {
   if x <= 1 {
      return x;
   } else {
      return x*fact(x-1);
   }
}
print("3! =", x);
```

## Loops
```blanc
let x = 0;
while x <= 100 {
   x = x + 1;
};
print("x =", x);
```
`note` break, continue statements are not supported yet


## Philosophy
**Here is our bloat take it or leave it**
no bold claims about replacing or tending to extend other languages

## Builtins
### Functions
`print`: accepts infinity amount of args and prints them to stdout separated by space
`prompt`: accepts a single argument of type of string, print it then read from stdin and returns the input as string
`time`: returns the amount of time elapsed from unix epoch

