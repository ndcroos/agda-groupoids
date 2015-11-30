{-# OPTIONS --without-K #-}

module Groupoids.Ambient.Groupoid.Initial where

open import Agda.Primitive
import Groupoids.Ambient.Groupoid.Base as G
import Groupoids.Setoid as S
import Groupoids.Type as T

g : ∀ {d} → G.t d lzero lzero lzero
G.obj g = T.𝟘.t
G.homˢ g = λ { (() T., _) }
G.idnˢ g = λ {}
G.cmpˢ g = λ {}
G.invˢ g = λ {}
G.idn-lhs g = λ {}
G.idn-rhs g = λ {}
G.cmp-ass g = λ {}
G.inv-lhs g = λ {}
G.inv-rhs g = λ {}
