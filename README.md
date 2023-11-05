# New Interpreter

This project is a rewrite of my previous project Toy Interpreter. The goal of both projects is to create a dynamic programming language that is a mix between Rust, Javascript and Python. While toy interpreter was implemented from scratch and without references as a challenge, new interpreter uses libraries for the parser and lexer as well as other components. This decision was made in order to speed up development and performance, since the goal of new interpreter is not so much learning as getting a usable language.


* The general syntax has been extracted from Rust: if, while, for, functions (fn, ||{})
* From Javascript I have extracted the syntax of objects and arrays.
* From Python I have extracted the name of some functions (print, range), the syntax of f-strings and the possibility to use the operators and, or and not.


A simple example of how to implement the Set data type in this programming language would be the following:

``` rust
Set = {
    new:|| {
        data:{},
        insert:|self,element| self.data[element]=0,
        contains:|self,element| contains(self.data,element),
        as_list:|self| {
            list = []
            for i in self.data {
                list.push(i[0])
            }
            list
        },
        to_string:|self| self.as_list().join(", ")
        
    },
    from_iter: |iter| {
        s = Set.new()
        for i in iter {
            s.insert(i)
        }
        s
    }
}

s = Set.from_iter([4,5,3,1,2,12,4,5,5])
print(s.to_string())
```