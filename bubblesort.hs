module Bubblesort where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

bubble :: (List Nat) -> List Nat
bubble l =
  and_rec (\_ _ l0 ->
    let {
     hrec l1 =
       case l1 of {
        Nil -> Nil;
        Cons n l2 ->
         case l2 of {
          Nil -> Cons n Nil;
          Cons n0 l3 ->
           case leb n n0 of {
            True ->
             sig_rec (\rec_res _ -> Cons n rec_res) (hrec (Cons n0 l3));
            False ->
             sig_rec (\rec_res _ -> Cons n0 rec_res) (hrec (Cons n l3))}}}}
    in hrec l0) l

bs :: (List Nat) -> List Nat
bs l =
  case l of {
   Nil -> Nil;
   Cons h l' -> bubble (Cons h (bs l'))}

