module Semantics where


open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using (⊤; tt)

import ITT as T
import 2LITT as 2T

-- Contexts are interpreted as presheaves over T.ICon
𝔼-ConI : 2T.ICon → T.ICon → Set
𝔼-Con : ∀ {IΓ IΔ} → 2T.Con IΓ → 𝔼-ConI IΓ IΔ → T.Con IΔ → Set

𝔼-TyM : ∀ {Γ} → 2T.TyM Γ → ∀ {Δ} → 𝔼-ConI Γ Δ → Set
𝔼-TyO : ∀ {Γ} → 2T.TyO Γ → ∀ {Δ} → 𝔼-ConI Γ Δ → T.Ty Δ

𝔼-ConI 2T.∙ IΔ = ⊤
𝔼-ConI (IΓ 2T.,M A) IΔ = Σ[ γI ∈ 𝔼-ConI IΓ IΔ ] 𝔼-TyM A γI
𝔼-ConI (IΓ 2T.,O A) IΔ = Σ[ γI ∈ 𝔼-ConI IΓ IΔ ] T.ITm IΔ (𝔼-TyO A γI)

𝔼-Con {IΓ = 2T.∙} 2T.∙ γI Δ
  = ⊤
𝔼-Con {IΓ = (IΓ 2T.,M A)} (Γ 2T.,M A) (γI , _) Δ
  = Σ[ γ ∈ 𝔼-Con Γ γI Δ ] 𝔼-TyM A γI
𝔼-Con {IΓ = (IΓ 2T.,O A)} (Γ 2T.,O A) (γI , a) Δ
  = Σ[ γ ∈ 𝔼-Con Γ γI Δ ] T.Tm Δ (𝔼-TyO A γI) a
𝔼-Con {IΓ = (IΓ 2T.,O A)} {IΔ} (Γ 2T.,OI A) (γI , _) Δ
  = Σ[ γ ∈ 𝔼-Con Γ γI Δ ] T.ITm IΔ (𝔼-TyO A γI)
