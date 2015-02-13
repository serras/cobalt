{-# LANGUAGE DataKinds, TypeOperators, GADTs, TypeFamilies, PolyKinds #-}
module Record where

data Field name ty = Field

data Record r where
  RNil  :: Record '[]
  RCons :: Field name ty -> ty -> Record rest -> Record (Field name ty ': rest)

type family Elem x lst where
  Elem x '[]         = False
  Elem x (x ': rest) = True
  Elem x (y ': rest) = Elem x rest

get :: Elem (Field name ty) r ~ True => Field name ty -> Record r -> ty
get = undefined

name = Field :: Field "name" String
age  = Field :: Field "age"  Integer

alex = RCons name "Alejandro" (RCons age 26 RNil)
jur  = RCons name "Jurriaan" RNil
