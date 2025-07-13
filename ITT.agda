module ITT where

-- Definition of a CWF with irrelevant binders in Agda, in the style of QTT.
----------------------------------------------------------------------------

-- The CWF formulation of quantitative type theory (Atkey 2I18) is basically a
-- base CWF B, a resourced CWF-like thing E, and a functor U : E → B that
-- preserves everything.
--
-- It is really annoying to define this directly as two syntaxes and a functor
-- between them because we need tons of coherence conditions for U. Instead, we
-- can define a base CWF B, and a displayed CWF E over B. We can recover the
-- usual functorial formulation by taking the total space of E.
--
-- The presented syntax below is basically QTT with the {I, ω} semiring. This
-- can be generalised to an arbitrary semiring if the context rules are modified
-- appropriately.
--
-- All equations CWF are omitted for brevity but can be added either as separate
-- relations or HIT equality constructors.

-- Base CWF sorts
data ICon : Set
data Ty : ICon → Set
data ISub : ICon → ICon → Set
data ITm : ∀ IΓ → Ty IΓ → Set

-- Displayed CWF sorts
data Con : ICon → Set
data Sub : ∀ {IΓ IΔ} → Con IΓ → Con IΔ → ISub IΓ IΔ → Set
data Tm : ∀ {IΓ} → (Γ : Con IΓ) → (A : Ty IΓ) → ITm IΓ A → Set

variable  
  IΓ IΓ' IΔ IΔ' : ICon
  Γ Γ' Δ Δ' : Con _
  A A' B B' : Ty _
  Ia Ia' Ib Ib' : ITm _ _
  a a' b b' : Tm _ _ _
  Iσ Iσ' Iσ'' : ISub _ _
  σ σ' σ'' : Sub _ _ _

data ICon where
  ∙ : ICon
  _,_ : ∀ IΓ → Ty IΓ → ICon
  
data Ty where
  _[_] : Ty IΔ → ISub IΓ IΔ → Ty IΓ

  U : Ty IΓ
  El : ITm IΓ U → Ty IΓ

  Π : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  ΠI : (A : Ty IΓ) → Ty (IΓ , A) → Ty IΓ
  
data ISub where
  id : ISub IΓ IΓ
  _∘_ : ISub IΓ IΓ' → ISub IΔ IΓ → ISub IΔ IΓ'

  p : ISub (IΓ , A) IΓ
  _,_ : (Iσ : ISub IΓ IΔ) → ITm IΓ (A [ Iσ ]) → ISub IΓ (IΔ , A)

  ε : ISub IΓ ∙
  
data ITm where
  _[_] : ITm IΔ A → (Iσ : ISub IΓ IΔ) → ITm IΓ (A [ Iσ ])
  q : ITm (IΓ , A) (A [ p ])

  lam : ITm (IΓ , A) B → ITm IΓ (Π A B)
  app : ITm IΓ (Π A B) → ITm (IΓ , A) B 

  lamI : ITm (IΓ , A) B → ITm IΓ (ΠI A B)
  appI : ITm IΓ (ΠI A B) → ITm (IΓ , A) B 
  
-- Displayed CWF constructors

data Con where
  ∙ : Con ∙
  _,_ : ∀ {IΓ} → (Γ : Con IΓ) → (A : Ty IΓ) → Con (IΓ , A)
  _,I_ : ∀ {IΓ} → (Γ : Con IΓ) → (A : Ty IΓ) → Con (IΓ , A)
  
data Sub where
  id : Sub Γ Γ id
  _∘_ : Sub Γ Γ' Iσ → Sub Δ Γ Iσ' → Sub Δ Γ' (Iσ ∘ Iσ')
  ε : Sub Γ ∙ ε
  
  p : Sub (Γ , A) Γ p
  _,_ : (σ : Sub Γ Δ Iσ) → Tm Γ (A [ Iσ ]) Ia → Sub Γ (Δ , A) (Iσ , Ia)

  pI : Sub (Γ ,I A) Γ p
  _,I_ : (σ : Sub Γ Δ Iσ) → (Ia : ITm IΓ (A [ Iσ ])) → Sub Γ (Δ ,I A) (Iσ , Ia)

data Tm where
  _[_] : Tm Δ A Ia → Sub Γ Δ Iσ → Tm Γ (A [ Iσ ]) (Ia [ Iσ ])
  q : Tm (Γ , A) (A [ p ]) q
  qI : Tm (Γ ,I A) (A [ p ]) q
  
  lam : Tm (Γ , A) B Ia → Tm Γ (Π A B) (lam Ia)
  app : Tm Γ (Π A B) Ia → Tm (Γ , A) B (app Ia)
  
  lamI : Tm (Γ ,I A) B Ia → Tm Γ (ΠI A B) (lamI Ia)
  appI : Tm Γ (ΠI A B) Ia → Tm (Γ ,I A) B (appI Ia)
  
  
-- Resourced CWF:

-- The formulation of QTT requires U to be a faithful functor but this is
-- not really necessary in general. We can even have different types above and below.

record RCon : Set where
  constructor _×_
  field
    Icon : ICon
    con : Con Icon

open RCon

𝐔 : RCon → ICon
𝐔 = Icon

record RSub (Γ : RCon) (Δ : RCon) : Set where
  constructor _×_
  field
    Isub : ISub (Γ .Icon) (Δ .Icon)
    sub : Sub (Γ .con) (Δ .con) Isub
    
open RSub
    
𝐔-sub : ∀ {Γ Δ} → RSub Γ Δ → ISub (𝐔 Γ) (𝐔 Δ)
𝐔-sub = Isub
    
record RTm (Γ : RCon) (A : Ty (𝐔 Γ)) : Set where
  constructor _×_
  field
    Itm : ITm (Γ .Icon) A
    tm : Tm (Γ .con) A Itm
    
open RTm

𝐔-tm : ∀ {Γ A} → RTm Γ A → ITm (𝐔 Γ) A
𝐔-tm = Itm