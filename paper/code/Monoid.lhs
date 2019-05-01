% -*- latex -*-
\begin{ignore}

> import Data.Monoid
> import Test.QuickCheck

> (+++) = mappend

\end{ignore}
The |Monoid| class, defined in the module |Data.Monoid| in Haskell's
base libraries, has the methods:

< mempty   :: a
< mappend  :: a -> a -> a

together with a method |mconcat :: [a] -> a| which we won't use in
this paper.
%
We will write infix |+++| for |mappend|.
%
Implementations of these methods in an instance of |Monoid| should
satisfy the following three laws:

<  mempty +++ m           = m
<  m +++ mempty           = m
<  l +++ (m +++ r)        = (l +++ m) +++ r
