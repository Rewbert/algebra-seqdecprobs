% -*- latex -*-
\begin{figure}

> class Functor f where
>   fmap :: (a -> b) -> f a -> f b

The |Functor| class is used for types that can be mapped over.
Instances of |Functor| should satisfy the following laws:

<    fmap id       ==  id
<    fmap (f . g)  ==  fmap f . fmap g

The instances of the class |Functor| for lists, |Data.Maybe.Maybe| and
|System.IO.IO| satisfy these laws.

\caption{Specification of the |Functor| class in the Haskell report \cite{haskell2010}.}
\label{functorspec}
\end{figure}

