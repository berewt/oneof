module Data.Subset

import Data.List
import Data.Sub

%default total

data Subset : List a -> Type where
  Here  : (x : a)   -> Subset (x::xs)
  There : Subset xs -> Subset (x::xs)

unwrap : Subset xs -> (x ** Elem x xs)
unwrap (Here x) = (x ** Here)
unwrap (There y) = case (unwrap y) of
                        (x ** pf) => (x ** There pf)

fromElem : Elem x xs -> Subset xs
fromElem {x} Here = Here x
fromElem (There later) = There (fromElem later)

restrict : (x : a) -> {auto prf : Elem x xs} -> Subset xs
restrict _ {prf} = fromElem prf

mapElem : Elem x xs -> Sub xs ys -> Elem x ys
mapElem Here (Here :: _) = Here
mapElem Here ((There later) :: _) = There later
mapElem (There later) (x :: y) = mapElem later y

relax : Subset xs -> {auto prf : Sub xs ys} -> Subset ys
relax x {prf} with (unwrap x) | (_ ** loc) = fromElem (mapElem loc prf)
