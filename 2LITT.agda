module 2LITT where

-- Definition of a 2-level CWF with irrelevant binders

-- Strategy: both base and displayed CWF are 2LTTs
-- the projection is the identity for the meta-fragment of the displayed CWF.

-- Base CWF sorts (irrelevant data)
data ICon : Set
data TyM : ICon → Set
data TyO : ICon → Set
data ISub : ICon → ICon → Set
data ITmM : ∀ IΓ → TyM IΓ → Set
data ITmO : ∀ IΓ → TyO IΓ → Set

-- Displayed CWF sorts (relevant data)
data Con : ICon → Set
data Sub : ∀ {IΓ IΔ} → Con IΓ → Con IΔ → ISub IΓ IΔ → Set
data TmM : ∀ {IΓ} → (Γ : Con IΓ) → (A : TyM IΓ) → ITmM IΓ A → Set
data TmO : ∀ {IΓ} → (Γ : Con IΓ) → (A : TyO IΓ) → ITmO IΓ A → Set

variable  
  IΓ IΓ' IΔ IΔ' : ICon
  Γ Γ' Δ Δ' : Con _
  A A' B B' : TyM _
  AO AO' BO BO' : TyO _
  Ia Ia' Ib Ib' : ITmM _ _
  IaO IaO' IbO IbO' : ITmO _ _
  a a' b b' : TmM _ _ _
  aO aO' bO bO' : TmO _ _ _
  Iσ Iσ' Iσ'' : ISub _ _
  σ σ' σ'' : Sub _ _ _

data ICon where
  ∙ : ICon
  _,M_ : ∀ IΓ → TyM IΓ → ICon
  _,O_ : ∀ IΓ → TyO IΓ → ICon
  
data TyM where
  _[_] : TyM IΔ → ISub IΓ IΔ → TyM IΓ

  U : TyM IΓ
  El : ITmM IΓ U → TyM IΓ

  Π : (A : TyM IΓ) → TyM (IΓ ,M A) → TyM IΓ
  
  ↑ : TyO IΓ → TyM IΓ
  
data TyO where
  _[_] : TyO IΔ → ISub IΓ IΔ → TyO IΓ

  U : TyO IΓ
  El : ITmO IΓ U → TyO IΓ

  Π : (A : TyO IΓ) → TyO (IΓ ,O A) → TyO IΓ
  ΠI : (A : TyO IΓ) → TyO (IΓ ,O A) → TyO IΓ
  
data ISub where
  id : ISub IΓ IΓ
  _∘_ : ISub IΓ IΓ' → ISub IΔ IΓ → ISub IΔ IΓ'

  pM : ISub (IΓ ,M A) IΓ
  _,M_ : (Iσ : ISub IΓ IΔ) → ITmM IΓ (A [ Iσ ]) → ISub IΓ (IΔ ,M A)

  pO : ISub (IΓ ,O AO) IΓ
  _,O_ : (Iσ : ISub IΓ IΔ) → ITmO IΓ (AO [ Iσ ]) → ISub IΓ (IΔ ,O AO)

  ε : ISub IΓ ∙
  
data ITmM where
  _[_] : ITmM IΔ A → (Iσ : ISub IΓ IΔ) → ITmM IΓ (A [ Iσ ])
  q : ITmM (IΓ ,M A) (A [ pM ])

  lam : ITmM (IΓ ,M A) B → ITmM IΓ (Π A B)
  app : ITmM IΓ (Π A B) → ITmM (IΓ ,M A) B 
  
  ⟨_⟩ : ITmO IΓ AO → ITmM IΓ (↑ AO)
  
data ITmO where
  _[_] : ITmO IΔ AO → (Iσ : ISub IΓ IΔ) → ITmO IΓ (AO [ Iσ ])
  q : ITmO (IΓ ,O AO) (AO [ pO ])

  lam : ITmO (IΓ ,O AO) BO → ITmO IΓ (Π AO BO)
  app : ITmO IΓ (Π AO BO) → ITmO (IΓ ,O AO) BO 

  lamI : ITmO (IΓ ,O AO) BO → ITmO IΓ (ΠI AO BO)
  appI : ITmO IΓ (ΠI AO BO) → ITmO (IΓ ,O AO) BO

  ~_ : ITmM IΓ (↑ AO) → ITmO IΓ AO
  
-- Displayed CWF constructors

data Con where
  ∙ : Con ∙
  _,M_ : ∀ {IΓ} → (Γ : Con IΓ) → (A : TyM IΓ) → Con (IΓ ,M A)
  _,OI_ : ∀ {IΓ} → (Γ : Con IΓ) → (A : TyO IΓ) → Con (IΓ ,O A)
  _,O_ : ∀ {IΓ} → (Γ : Con IΓ) → (A : TyO IΓ) → Con (IΓ ,O A)
  
data Sub where
  id : Sub Γ Γ id
  _∘_ : Sub Γ Γ' Iσ → Sub Δ Γ Iσ' → Sub Δ Γ' (Iσ ∘ Iσ')
  ε : Sub Γ ∙ ε
  
  -- Meta
  p : Sub (Γ ,M A) Γ pM
  _,_ : (σ : Sub Γ Δ Iσ) → TmM Γ (A [ Iσ ]) Ia → Sub Γ (Δ ,M A) (Iσ ,M Ia)
  
  -- Relevant object
  pO : Sub (Γ ,O AO) Γ pO
  _,O_ : (σ : Sub Γ Δ Iσ) → TmO Γ (AO [ Iσ ]) IaO → Sub Γ (Δ ,O AO) (Iσ ,O IaO)

  -- Irrelevant object
  pOI : Sub (Γ ,OI AO) Γ pO
  _,OI_ : (σ : Sub Γ Δ Iσ) → (IaO : ITmO IΓ (AO [ Iσ ])) → Sub Γ (Δ ,OI AO) (Iσ ,O IaO)

data TmM where
  _[_] : TmM Δ A Ia → Sub Γ Δ Iσ → TmM Γ (A [ Iσ ]) (Ia [ Iσ ])
  q : TmM (Γ ,M A) (A [ pM ]) q
  
  lam : TmM (Γ ,M A) B Ia → TmM Γ (Π A B) (lam Ia)
  app : TmM Γ (Π A B) Ia → TmM (Γ ,M A) B (app Ia)
  
  ⟨_⟩ : TmO Γ AO IaO → TmM Γ (↑ AO) ⟨ IaO ⟩

data TmO where
  _[_] : TmO Δ AO IaO → Sub Γ Δ Iσ → TmO Γ (AO [ Iσ ]) (IaO [ Iσ ])
  qO : TmO (Γ ,O AO) (AO [ pO ]) q
  
  lam : TmO (Γ ,O AO) BO IaO → TmO Γ (Π AO BO) (lam IaO)
  app : TmO Γ (Π AO BO) IaO → TmO (Γ ,O AO) BO (app IaO)
  
  lamI : TmO (Γ ,OI AO) BO IaO → TmO Γ (Π AO BO) (lam IaO)
  appI : TmO Γ (Π AO BO) IaO → TmO (Γ ,OI AO) BO (app IaO)
  
  ~_ : TmM Γ (↑ AO) Ia → TmO Γ AO (~ Ia)
  