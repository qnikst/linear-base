In last post we have checked how we can use reflection framework in
order to sort list, and used 'SortedList' structure inside. But even
we used this special structure sorting is not guaranteed to be safe
as theoretically implmentation can lose elements or duplicate them.

Ideally we want an implementation that is guaranteed to be a reordering
of the incoming elemnts. There are some ways to do that:
  
  * just trust the code
  * use liquid haskell and prove the code
  * use linear types together with code that returns AscList.

The key idea here is that if we have linear parametric structure, then
and return the structure of the same type it's guaranteed that it will
be reordering. In this case we want to use linear types extension to ghc.
And it may be an interesting experiment about how to get additional guarantees
from the extention that didn't have this feature in mind (??).

An interesting use of the linear types here is that we will not
consume values at all instead we want the guarantee that they
are not consumed in our code (if they are properly consumed somewhere
later).

This is literate haskell file and can be compiled by ghci with
linear-types extension enabled.

> {-# LANGUAGE ViewPatterns #-}
> {-# LANGUAGE ScopedTypeVariables #-} -- for merge
> {-# LANGUAGE UndecidableInstances #-} -- For OrdL
> {-# LANGUAGE FlexibleInstances #-} -- For OrdL
> {-# LANGUAGE DefaultSignatures #-}
> {-# LANGUAGE BangPatterns      #-}

> import Prelude.Linear
> import Unsafe.Linear as Unsafe
> import Data.Ord

We will reuse types from the previous post.

> newtype SortedList a = Sorted [a]
>
> forget :: SortedList a ->. [a]
> forget (Sorted l) = l
>
> nil :: SortedList a
> nil = Sorted []
>
> singleton :: a ->. SortedList a
> singleton a = Sorted [a]

The first quesion is how can we actually compare the elements.
Recall the types of the usual `compare` function, it is:

```
compare :: Ord a => a -> a -> Ordering
```

we can't just lift this method to a linear types, because it
will consume values and we can't use them in further code.
In order to solve this problem properly we need to have a notion
of `borrow`ing. I.e. ability to pass value to method but without
passing ownership, so that method can't free it. Currently
compiler and proposal does not have notion of borrowing, but
we can encode it using linear types, for the method with signature
`foo :: a -> b` we can introduce method `fooL :: a -> (a, b)` that
will return back value that was passed, so it's guaranteed that
it was not totally consumed. It's possible that in final extension
we will have helpers or utilities that would allow to help us with
removing boilerplate code.

So now we need to introduce new typeclass that will be a linear
variant of the ordinary `Ord` class. (In future releases that will
not be needed and we would be able to just use Ord ?)


> class OrdL a where
>   -- | Compares the elements and their 'Ordering' and values
>   -- that are by convention in the sorted order.
>   compareL :: a ->. a ->. (Ordering, a, a)

I'm not sure that this is an ideal type (thus it's not in linear-base)
but at least it would fit our needs.

>   default compareL :: (Ord a, Movable a) => a ->. a ->. (Ordering, a, a)
>   compareL a b = go (dup a) (dup b) where
>     go :: (Movable a, Ord a) => (a, a) ->. (a, a) ->. (Ordering, a, a)
>     go (a', as) (b', bs) = go' a' b' (move as) (move bs)
>     go' :: Ord a => a ->. a ->. Unrestricted a ->. Unrestricted a ->. (Ordering, a, a)
>     go' a' b' (Unrestricted as) (Unrestricted bs) = 
>       go'' a' b' (compare as bs)
>     go'' :: a ->. a ->. Ordering ->. (Ordering, a, a)
>     go'' a' b' EQ = (EQ, a', b')
>     go'' a' b' GT = (GT, a', b')
>     go'' a' b' LT = (LT, a', b')

TODO: Consumable, Dupable, Movable


Now we are ready to implement merge sort. Merge sort has two steps:
1. split list into 2 sublists and 2. merge sorted sublists.

Lets implement split first:

> split :: [a] ->. ([a], [a])
> split []      = ([], [])
> split [x]     = ([x], [])
> split (x:y:z) = go (x,y) (split z) where
>   go :: (a,a) ->. ([a], [a]) ->. ([a], [a])
>   go (a,b) (c,d) = (a:c, b:d)

We split list into 2 parts by moving all elements with even position
in one sublist and ones with odd into the other. This way we should
not count the size of the list and can do split in streaming fasion.

Actually it's possible to implenet `split` without introducing the
helper function, but it's needed at the current stage because support
in compiler is premature.

> view1 :: SortedList a ->. (a, SortedList a)
> view1 (Sorted (a:as)) = (a, Sorted as)

> merge :: forall a. OrdL a  => SortedList a ->. SortedList a ->. SortedList a
> merge (Sorted []) bs = bs
> merge as (Sorted []) = as
> merge (view1 -> (a, as)) (view1 -> (b, bs)) = go (compareL a b) as bs where
>   go :: (Ordering, a, a) ->. SortedList a ->. SortedList a ->. SortedList a
>   go (EQ,k,l) ks ls = Sorted (k: l : forget (merge ks ls))
>   go (LT,k,l) ks ls = Sorted (k: forget (merge ks (Sorted (l: forget ls))))
>   go (GT,l,k) ks ls = Sorted (l: forget (merge (Sorted (k: forget ks)) ls))

Recall wahat we had in non-linear case:

```
-> merge :: Ord a => SortedList a -> SortedList a -> SortedList a
-> merge (Sorted left0) (Sorted right0) = Sorted $ mergeList left0 right0 where
->   mergeList :: Ord a => [a] -> [a] -> [a]
->   mergeList [] right = right
->   mergeList left []  = left
->   mergeList left@(a:l) right@(b:r) =
->     if a <= b
->     then a: mergeList l right
->     else b: mergeList left r
```

> fromList :: forall a. OrdL a => [a] ->. SortedList a
> fromList [] = Sorted []
> fromList [a] = singleton a
> fromList xs = go1 (split xs) where
>  go1 :: ([a], [a]) ->. SortedList a
>  go1 (left, right) = merge (fromList left) (fromList right)

{-



-- | merge 2 lists.

data PQ key a = PE | PQ [(key,a)]

enqueue :: key -> a ->. PQ key a ->. PQ key a
enqueue key value PE = PQ [(key, value)]

dequeue :: PQ key a ->. (Maybe (key, a), PQ key a)
dequeue PE = (Nothing, PE)
dequeue (PQ (k:kv)) = (Just k, PQ kv)


> main = print "hello world"

  Prelude.$ getList
  Prelude.Linear.$ mergeSort [10,6,17,1::Int,2,3]
-}
