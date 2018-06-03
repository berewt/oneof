# oneof

Take advantage of Σ-types to define a type by enumerating its value.

For exemple : `OneOf ["foo", "bar"]` can only contains "foo" and "bar".

```idris
FooBar : Type
FooBar = OneOf ["foo", "bar"]

-- OK
foo : FooBar
foo = member "foo"

-- KO
baz : FooBar
baz = member "baz"
```

You can even "translate" a value

```idris
fooWider : OneOf ["bar", "baz", "foo"]
fooWider = translate foo
```

And "fold" the value of a `OneOf` thanks to a list of pairs:

```idris
answer : Nat
answer = foldOneOf [("foo", 42),("bar",54)] foo
```

You can also list all the elements of a 'OneOf':

```idris
fooBar : List FooBar
fooBar = allOf
```
