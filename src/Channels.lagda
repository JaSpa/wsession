\begin{code}[hide]
module Channels {ℓ} (IO : Set → Set ℓ) (⊤ : Set) where
{-# FOREIGN GHC import qualified Control.Concurrent.UntypedChannel as UC #-}
\end{code}
\newcommand\variableAB{%
\begin{code}
private variable A B C : Set
\end{code}}
\newcommand\postulateChannel{%
\begin{code}
postulate
  Channel    : Set
  primAccept : IO Channel
  primClose  : Channel → IO ⊤
  primSend   : A → Channel → IO ⊤
  primRecv   : Channel → IO A
\end{code}}
\begin{code}[hide]
  primFork   : IO ⊤ → IO ⊤

data Channel×Channel : Set where
  ⟨_,_⟩ : Channel → Channel → Channel×Channel
{-# COMPILE GHC Channel×Channel = data UC.CPairWrapper (UC.CPair) #-}

postulate
  newChan  : IO Channel×Channel
\end{code}
\begin{code}[hide]
{-# COMPILE GHC Channel = type UC.ChannelWrapper #-}
{-# COMPILE GHC primSend = \ _ -> UC.primSend #-}
{-# COMPILE GHC primRecv = \ _ -> UC.primRecv #-}
{-# COMPILE GHC primClose = UC.primClose #-}
{-# COMPILE GHC primFork = UC.primFork #-}
{-# COMPILE GHC newChan = UC.newChan #-}
\end{code}
