# csharp-expr-rs

c# expression parser in Rust


# Todo
- [x] Parse expressions with nom parser
- [x] Execute expressions
- [x] FFI create an expression from .net
- [x] Execute this expression from .net
- [x] Benchmark execution time against DynamicExpresso (.net expression interpreter) => .net version x2 better
- [x] Optimize so function are ready to call after first parsing => Rust now competes with DynamicExpresso
- [x] Benchmark "compilation" time => Rust x40 better
- [x] Debug trait for Expr
- [x] PartialEq trait for Expr
- [x] Parse '"str\"ing"' as 'str"ing' value for Exp::Str (tried escaped_transfom but it changes the return types, perhaps find an other way, when creating the Expr::Str)
- [x] More unit tests (Rust side)
- [x] Handle identifiers
- [x] Handle identifier value and usage
- [x] Handle passing values arguments for identifiers from C# side
- [x] Benchmarks & Optimisations => cloning Expressions was a baaaaaad idea ! /10 perfs drop
- [x] Could we try some better syntax with type aliasing Rc<Expr>, perhaps some macros ? okay, not bad, not great
- [x] Optimisation : Do not pass parameters throught FFI if they are not used by the expression !
- [x] More tests about identifiers list
- [x] Couldn't prepare a function inside an unknown function => OK, expected behavior
- [x] Handle `null` value (just in case)
- [ ] Implement existing functions in BZP system & compare performances
- [ ] Implement Sql Like function
- [ ] Debug Identifiers (Some tests are not passing)
- [ ] More perf benchmarks with arguments passing
- [ ] Optimisation : lazy evaluation for identifier value getters ? https://docs.rs/once_cell/1.2.0/once_cell/
- [ ] Error handling on expressions parsing
- [ ] Result/Error handling on FFI for expressions execution
- [ ] Modularisation, so anyone can implement their own functions list
- [ ] Case insensitive function names
- [ ] Handle Assoc/Binary operators
- [ ] Handle numeric types as Decimal/Money with 4 digits precision (have to find the right crate)
- [ ] Publish on crates.io


# Super helpfull resources
- http://jakegoulding.com/rust-ffi-omnibus/
- https://dev.to/living_syn/calling-rust-from-c-6hk
- https://dev.to/luzero/building-crates-so-they-look-like-c-abi-libraries-1ibn
- https://ndportmann.com/system-runtime-compilerservices-unsafe/

# more reading ?
- https://bodil.lol/parser-combinators/