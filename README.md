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
- [ ] Handle passing values arguments for identifiers from C# side
- [ ] Debug Identifiers (Some tests are not passing)
- [ ] More perf benchmarks with arguments passing
- [ ] Error handling on expressions parsing
- [ ] Result/Error handling on FFI for expressions execution
- [ ] Modularisation, so anyone can implement their own functions list
- [ ] Implement existing functions in BZP system & compare performances
- [ ] Handle Assoc/Binary operators
- [ ] Handle numeric types as Decimal/Money with 4 digits precision (have to find the right crate)
- [ ] Publish on crates.io


# Super helpfull resources
- https://dev.to/living_syn/calling-rust-from-c-6hk
- http://jakegoulding.com/rust-ffi-omnibus/
- https://dev.to/luzero/building-crates-so-they-look-like-c-abi-libraries-1ibn

# more reading ?
- https://bodil.lol/parser-combinators/