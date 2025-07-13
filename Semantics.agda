module Semantics where

open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using (⊤; tt)

import ITT as T
import 2LITT as 2T

variable
  IΓ IΓ' : 2T.ICon
  IΔ IΔ' : T.ICon
  Γ Γ' : 2T.Con _
  Δ Δ' : T.Con _
  A A' : 2T.TyM _
  AO AO' : 2T.TyO _
  Ia Ia' : 2T.ITmM _ _
  IaO IaO' : 2T.ITmO _ _
  a a' : 2T.TmM _ _ _
  aO aO' : 2T.TmO _ _ _

-- Elimination motives:

-- Irrelevant

𝔼-ICon : 2T.ICon → T.ICon → Set
𝔼-ICon-$ : (IΓ : 2T.ICon) → ∀ {IΔ} {IΔ'}
  → T.ISub IΔ IΔ'
  → 𝔼-ICon IΓ IΔ'
  → 𝔼-ICon IΓ IΔ

𝔼-ISub : (IΓ : 2T.ICon) → (IΓ' : 2T.ICon) → ∀ {IΔ} → 𝔼-ICon IΓ IΔ → 𝔼-ICon IΓ' IΔ

𝔼-TyM : 2T.TyM IΓ → ∀ {IΔ} → 𝔼-ICon IΓ IΔ → Set
𝔼-TyM-$ : (A : 2T.TyM IΓ) → ∀ {IΔ} {IΔ'}
  → (σ : T.ISub IΔ IΔ')
  → {γ : 𝔼-ICon IΓ IΔ'}
  → 𝔼-TyM A γ
  → 𝔼-TyM A (𝔼-ICon-$ IΓ σ γ)

𝔼-TyO : 2T.TyO IΓ → ∀ {IΔ} → 𝔼-ICon IΓ IΔ → T.Ty IΔ
𝔼-TyO-$ : (AO : 2T.TyO IΓ) → ∀ {IΔ} {IΔ'}
  → (σ : T.ISub IΔ IΔ')
  → {γ : 𝔼-ICon IΓ IΔ'}
  → T.ITm IΔ' (𝔼-TyO AO γ)
  → T.ITm IΔ (𝔼-TyO AO (𝔼-ICon-$ IΓ σ γ))

𝔼-ITmM : 2T.ITmM IΓ A → ∀ {IΔ} → (Iγ : 𝔼-ICon IΓ IΔ) → 𝔼-TyM A Iγ

𝔼-ITmO : 2T.ITmO IΓ AO → ∀ {IΔ} → (Iγ : 𝔼-ICon IΓ IΔ) → T.ITm IΔ (𝔼-TyO AO Iγ)

-- Relevant

𝔼-Con : 2T.Con IΓ → ∀ {IΔ} → 𝔼-ICon IΓ IΔ → T.Con IΔ → Set

𝔼-Sub : (Γ : 2T.Con IΓ) → (Γ' : 2T.Con IΓ')
  → 2T.ISub IΓ IΓ'
  → ∀ {IΔ} {Iγ : 𝔼-ICon IΓ IΔ} {Δ : T.Con IΔ}
  → 𝔼-Con Γ Iγ Δ → 𝔼-Con Γ' (𝔼-ISub IΓ IΓ' Iγ) Δ

𝔼-TmM : 2T.TmM Γ A Ia
  → ∀ {IΔ} {Iγ : 𝔼-ICon IΓ IΔ} {Δ : T.Con IΔ}
  → 𝔼-Con Γ Iγ Δ → 𝔼-TyM A Iγ

𝔼-TmO : 2T.TmO Γ AO IaO
  → ∀ {IΔ} {Iγ : 𝔼-ICon IΓ IΔ} {Δ : T.Con IΔ}
  → 𝔼-Con Γ Iγ Δ → T.Tm Δ (𝔼-TyO AO Iγ) (𝔼-ITmO IaO Iγ)

-- Elimination methods

-- Irrelevant

𝔼-ICon 2T.∙ IΔ = ⊤
𝔼-ICon (IΓ 2T.,M A) IΔ = Σ[ Iγ ∈ 𝔼-ICon IΓ IΔ ] 𝔼-TyM A Iγ
𝔼-ICon (IΓ 2T.,O A) IΔ = Σ[ Iγ ∈ 𝔼-ICon IΓ IΔ ] T.ITm IΔ (𝔼-TyO A Iγ)

𝔼-ICon-$ 2T.∙ σ tt = tt
𝔼-ICon-$ (IΓ 2T.,M A) σ (γ , a) = (𝔼-ICon-$ IΓ σ γ , 𝔼-TyM-$ A σ a)
𝔼-ICon-$ (IΓ 2T.,O AO) σ (γ , aO) = (𝔼-ICon-$ IΓ σ γ , 𝔼-TyO-$ AO σ aO)

-- Relevant

𝔼-Con 2T.∙ _ Δ = ⊤
𝔼-Con (Γ 2T.,M A) (Iγ , _) Δ = Σ[ γ ∈ 𝔼-Con Γ Iγ Δ ] 𝔼-TyM A Iγ
𝔼-Con (Γ 2T.,O A) (Iγ , a) Δ = Σ[ γ ∈ 𝔼-Con Γ Iγ Δ ] T.Tm Δ (𝔼-TyO A Iγ) a
𝔼-Con (Γ 2T.,OI A) {IΔ} (Iγ , _) Δ = Σ[ γ ∈ 𝔼-Con Γ Iγ Δ ] T.ITm IΔ (𝔼-TyO A Iγ)

