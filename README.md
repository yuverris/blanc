# blanc
yet another (WIP) programming language

# Example
```blanc
print("hello, world!");
```

# Data types
```blanc
1; // integer

3.14; // float

true;
false; // bool

"hello"; // string

'a'; // char

[1,2,3, true, ..]; // array

{"hello": 5}; // map soon™

(12, "hello", false, "there"); // tuple soon™
```

# Variables
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

# Functions
functions are prefixed with the `fnc` keyword

```blanc
fnc get_1() {
    return 1;
};
fnc get_2() {
    return 2;
};
print(get_1() + get_2());
```

# Control Flow
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

# Loops
```blanc
let x = 0;
while x <= 100 {
   x = x + 1;
};
print("x =", x);
```
`note` break, continue statements are not supported yet

and that's all for now.
