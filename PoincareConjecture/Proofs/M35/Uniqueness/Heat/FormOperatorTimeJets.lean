import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawOperatorSmooth
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CoefficientTimeJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative

theorem hasDerivWithinAt_clm_sandwich
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : F →L[ℝ] G) (R : H →L[ℝ] E) {A : ℝ → E →L[ℝ] F} {d : E →L[ℝ] F}
    {S : Set ℝ} {t : ℝ} (hA : HasDerivWithinAt A d S t) :
    HasDerivWithinAt (fun s => L.comp ((A s).comp R)) (L.comp (d.comp R)) S t := by
  have h := (hasDerivWithinAt_const t S L).clm_comp
    (hA.clm_comp (hasDerivWithinAt_const t S R))
  simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
    zero_add, add_zero] using h

variable {n m : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem hasDerivWithinAt_principalFormOperator (K : Set X)
    (A : ℝ → Fin n → Fin n → 𝓢(X, ℝ)) (d : Fin n → Fin n → 𝓢(X, ℝ))
    {S : Set ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivWithinAt (fun s => schwartzMultiplier (A s i j))
      (schwartzMultiplier (d i j)) S t) :
    HasDerivWithinAt (fun s => principalFormOperator K (A s))
      (principalFormOperator K d) S t := by
  unfold principalFormOperator
  exact HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
    hasDerivWithinAt_clm_sandwich (dirichletPartialAdjoint K i)
      (dirichletPartial K j) (hA i j)))

theorem hasDerivWithinAt_dirichletLowerOrder {K : Set X} (hK : IsClosed K)
    (B : ℝ → Fin n → 𝓢(X, ℝ)) (C : ℝ → 𝓢(X, ℝ))
    (dB : Fin n → 𝓢(X, ℝ)) (dC : 𝓢(X, ℝ)) {S : Set ℝ} {t : ℝ}
    (hB : ∀ i, HasDerivWithinAt (fun s => dirichletValueMultiplier K (B s i))
      (dirichletValueMultiplier K (dB i)) S t)
    (hC : HasDerivWithinAt (fun s => dirichletValueMultiplier K (C s))
      (dirichletValueMultiplier K dC) S t) :
    HasDerivWithinAt (fun s => dirichletLowerOrder hK (B s) (C s))
      (dirichletLowerOrder hK dB dC) S t := by
  have hfirst (i : Fin n) := (hB i).clm_comp
    (hasDerivWithinAt_const t S (dirichletPartialValue hK i))
  have hzero := hC.clm_comp (hasDerivWithinAt_const t S (dirichletInclusion K))
  simpa only [dirichletLowerOrder, ContinuousLinearMap.comp_zero, add_zero,
    ] using
    (HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hfirst i)).fun_add hzero

theorem hasDerivWithinAt_finiteHilbertMatrix
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : ℝ → Fin m → Fin m → E →L[ℝ] F) (d : Fin m → Fin m → E →L[ℝ] F)
    {S : Set ℝ} {t : ℝ} (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (d i j) S t) :
    HasDerivWithinAt (fun s => finiteHilbertMatrix (A s)) (finiteHilbertMatrix d) S t := by
  unfold finiteHilbertMatrix
  exact HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun i _ => HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
    hasDerivWithinAt_clm_sandwich (finiteHilbertSingle i)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => E) j) (hA i j)))

theorem hasDerivWithinAt_dirichletVectorLowerOrder {K : Set X} (hK : IsClosed K)
    (B : ℝ → Fin m → Fin m → Fin n → 𝓢(X, ℝ))
    (C : ℝ → Fin m → Fin m → 𝓢(X, ℝ))
    (dB : Fin m → Fin m → Fin n → 𝓢(X, ℝ)) (dC : Fin m → Fin m → 𝓢(X, ℝ))
    {S : Set ℝ} {t : ℝ}
    (hB : ∀ i j k, HasDerivWithinAt (fun s => dirichletValueMultiplier K (B s i j k))
      (dirichletValueMultiplier K (dB i j k)) S t)
    (hC : ∀ i j, HasDerivWithinAt (fun s => dirichletValueMultiplier K (C s i j))
      (dirichletValueMultiplier K (dC i j)) S t) :
    HasDerivWithinAt (fun s => dirichletVectorLowerOrder hK (B s) (C s))
      (dirichletVectorLowerOrder hK dB dC) S t :=
  hasDerivWithinAt_finiteHilbertMatrix _ _ (fun i j =>
    hasDerivWithinAt_dirichletLowerOrder hK _ _ _ _ (hB i j) (hC i j))

end PoincareConjecture.M35.Uniqueness.Heat
