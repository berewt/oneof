module Data.OneOf

import public Data.Sub

%default total
%access export

||| Define a type that are inhabited exactly by the given list of value
public export
OneOf : (xs : List a) -> Type
OneOf = Exists . flip Elem

||| "lift" a value as a 'OneOf' as long as a proof that it's one of the listed
||| values can be provided
member : (x : a) -> {auto prf : Elem x xs} -> OneOf xs
member = Evidence

||| "unlift" the value of a 'OneOf'
unwrap : {xs : List a} -> OneOf xs -> a
unwrap (Evidence x _) = x

||| Move from one 'OneOf' value to another one, as soon as the new one contains
||| at least oll the values of the first one.
public export
translate : OneOf xs -> {auto prf : Sub xs ys} -> OneOf ys
translate (Evidence x pf) = Evidence x (mapElem pf)

||| Lise of keys/value used in the catamorphism of one of ('foldOneOf')
public export
data SubFold : (xs : List a) -> Type -> Type where
  Nil : SubFold [] a
  Cons : (x : a) -> (v : b) -> SubFold xs b -> SubFold (x::xs) b

private
foldOneOfSameOrder : SubFold xs a -> Elem x xs -> a
foldOneOfSameOrder Nil          Here          impossible
foldOneOfSameOrder Nil          (There later) impossible
foldOneOfSameOrder (Cons _ v _) Here          = v
foldOneOfSameOrder (Cons _ _ f) (There later) = foldOneOfSameOrder f later

||| Create a 'SubFold' from a list of values.
public export
fromList : (xs : List (k,v)) -> SubFold (map Prelude.Basics.fst xs) v
fromList [] = Nil
fromList ((x, y) :: xs) = Cons x y (fromList xs)

foldOneOf : {xs : List k} -> (ys : List (k,v)) -> OneOf xs -> {auto prf : Sub xs (map Prelude.Basics.fst ys)} -> v
foldOneOf f x = case (translate x) of
                     Evidence _ pf => foldOneOfSameOrder (fromList f) pf

||| Expand 'OneOf' by one element to its left.
shift : OneOf xs -> OneOf (x::xs)
shift (Evidence x pf) = Evidence x (There pf)

||| List all the inhabitants of a 'OneOf' type.
allOf : List (OneOf xs)
allOf {xs = []} = []
allOf {xs = (x::xs)} = Evidence x Here :: map shift allOf
