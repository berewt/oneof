module Data.OneOf

import public Data.List
import public Data.Sub

%default total
%access export

public export
OneOf : (xs : List a) -> Type
OneOf = Exists . flip Elem

member : (x : a) -> {auto prf : Elem x xs} -> OneOf xs
member = Evidence

unwrap : {xs : List a} -> OneOf xs -> a
unwrap (Evidence x _) = x

translate : OneOf xs -> {auto prf : Sub xs ys} -> OneOf ys
translate (Evidence x pf) = Evidence x (mapElem pf)

public export
data SubFold : (xs : List a) -> Type -> Type where
  Nil : SubFold [] a
  Cons : (x : a) -> (v : b) -> SubFold xs b -> SubFold (x::xs) b

private
foldOneOfSameOrder : SubFold xs a -> OneOf xs -> a
foldOneOfSameOrder Nil          (Evidence x Here)          impossible
foldOneOfSameOrder Nil          (Evidence x (There later)) impossible
foldOneOfSameOrder (Cons _ v _) (Evidence x Here)          = v
foldOneOfSameOrder (Cons _ _ f) (Evidence x (There later)) = foldOneOfSameOrder f (Evidence x later)

public export
fromList : (xs : List (k,v)) -> SubFold (map Prelude.Basics.fst xs) v
fromList [] = Nil
fromList ((x, y) :: xs) = Cons x y (fromList xs)

foldOneOf : {xs : List k} -> (ys : List (k,v)) -> OneOf xs -> {auto prf : Sub xs (map Prelude.Basics.fst ys)} -> v
foldOneOf f x = foldOneOfSameOrder (fromList f) (translate x)
