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
- [x] Debug ` ` white space and tabs in strings are still strings
- [x] Segregate Expr & ExprResult enum types
- [x] Implement Sql Like function
- [x] Implement existing functions in BZP system
- [x] Case insensitive function names ... and identifier names
- [x] Result/Error handling on FFI for expressions execution
- [x] Debug strings should be able to contain any character ! see also : https://github.com/Geal/nom/issues/1118 
- [x] Handle (good enough) non ascii strings
- [x] Handle numeric types as Decimal/Money with 4 digits precision (have to find the right crate : https://crates.io/crates/rust_decimal ?)
- [x] Debug empty parameters list parsing (it's parsed as identifier right now) 
- [x] Handle functions determinism
- [x] Debug empty string parsing
- [x] refacto : remove all usage of `opt(sp)`, the take_while in sp() should be enough do the optional trick
- [x] refacto : replace some preceded/terminated by 'delimited'
- [x] Handle C# Assoc/Binary operators parsing (only delimited by parenthesis)
- [x] Handle C# Assoc/Binary operators execution
- [x] Handle C# Assoc/Binary operators parsing with no parenthesis delimiter
- [x] Make FFI parse fail to return an error and raise a nice exception AND not panicking ! 
- [ ] Make C# FFI 1 char strings to Rust
- [ ] sp() should get the new lines and allow the parsing to continue
- [ ] Handle operators precedence !
- [ ] Replace &Vec usage by slices (have a look at f_operators)
- [ ] Turn all possible overflow problems in casts (isize as u32, i32 ....) to nice errors
- [ ] Make all default String lazy static or &str
- [ ] comment out or remove dbg!()
- [ ] Handle non usefull parenthesis (some tests to uncomment)
- [ ] Debug snake case identifiers parsing
- [ ] Debug Identifiers (Some tests are not passing)
- [ ] More perf benchmarks with arguments passing
- [ ] Return the right result type throught FFI
- [ ] Optimisation : lazy evaluation for identifier value getters ? https://docs.rs/once_cell/1.2.0/once_cell/
- [ ] Error handling on expressions parsing
- [ ] Modularisation, so anyone can implement their own functions list
- [ ] Allow passing functions from dotnet side to be called from rust expression ?    // see System.Runtime.InteropServices.AllowReversePInvokeCallsAttribute
- [ ] Publish on crates.io


# Super helpfull resources
- http://jakegoulding.com/rust-ffi-omnibus/
- https://dev.to/living_syn/calling-rust-from-c-6hk
- https://dev.to/luzero/building-crates-so-they-look-like-c-abi-libraries-1ibn
- https://ndportmann.com/system-runtime-compilerservices-unsafe/

# more reading ?
- https://bodil.lol/parser-combinators/
