\begin{code}[hide]
module Channels (IO : Set → Set₁) (⊤ : Set) where
\end{code}
\newcommand\variableAB{%
\begin{code}
variable A B C : Set
\end{code}}
\newcommand\postulateChannel{%
\begin{code}
postulate
  Channel : Set
  primAccept : IO Channel
  primClose : Channel → IO ⊤
  primSend : A → Channel → IO ⊤
  primRecv : Channel → IO A
  primFork : IO ⊤ → IO ⊤
\end{code}}
\begin{code}[hide]

data Channel×Channel : Set where
  ⟨_,_⟩ : Channel → Channel → Channel×Channel
{-# COMPILE GHC Channel×Channel = data UC.CPair (UC.CPair) #-}

postulate
  newChan  : IO Channel×Channel
\end{code}
\begin{code}[hide]
{-# COMPILE GHC Channel = type UC.Channel #-}
{-# COMPILE GHC primSend = \ _ -> UC.primSend #-}
{-# COMPILE GHC primRecv = \ _ -> UC.primRecv #-}
{-# COMPILE GHC primClose = UC.primClose #-}
{-# COMPILE GHC primFork = UC.primFork #-}
{-# COMPILE GHC newChan = UC.newChan #-}
\end{code}
