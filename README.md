# rustlyn
c# expression parser in Rust


# Todo
- [x] Debug trait for Expr
- [x] PartialEq trait for Expr
- [x] Parse '"str\"ing"' as 'str"ing' value for Exp::Str (tried escaped_transfom but it changes the return types, perhaps find an other way, when creating the Expr::Str)
- [ ] More unit tests (Rust side)
- [ ] Handle identifiers
- [ ] Handle passing values arguments for identifiers from C# side
- [ ] More perf benchmarks with arguments passing
- [ ] Modularisation, so anyone can implement their own functions list
- [ ] Implement existing functions in BZP system & compare performances
- [ ] Handle Assoc/Binary operators
- [ ] Handle numeric types as Decimal/Money with 4 digits precision (have to find the right crate)