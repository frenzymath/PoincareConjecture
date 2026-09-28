import PoincareConjecture.Proofs.M08.LinearIntervalODE
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff

universe uJacobi

namespace PoincareConjecture.M08

variable {E : Type uJacobi} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance jacobiPhaseDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiPhaseDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiPhaseBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiPhaseBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiPhaseTrilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiPhaseTrilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance jacobiPhaseQuadGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance jacobiPhaseQuadSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def jacobiCurvatureCovector (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (A : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) ℝ)
    (ContinuousLinearMap.apply ℝ ℝ A)).comp (R.flip A)

theorem jacobiCurvatureCovector_apply
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (A y w : E) :
    jacobiCurvatureCovector R A y w = R y A w A := rfl

def jacobiConnectionVariationCovector (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (A : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  N A + N.flip A - (N.flip A).flip

theorem jacobiConnectionVariationCovector_apply
    (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (A y w : E) :
    jacobiConnectionVariationCovector N A y w = N A y w + N y A w - N w A y := rfl

def jacobiPotentialCovector
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  -jacobiCurvatureCovector R A + (2 * s) • jacobiConnectionVariationCovector N A +
    (2 * s ^ 2) • H - (4 * s) • N.flip A

theorem jacobiPotentialCovector_apply
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A y w : E) :
    jacobiPotentialCovector R H N s A y w =
      -R y A w A + 2 * s * (N A y w + N y A w - N w A y) +
        2 * s ^ 2 * H y w - 4 * s * N y A w := rfl

def covariantLinearPhaseOperator (B : (E →L[ℝ] ℝ) →L[ℝ] E) (C : E →L[ℝ] E)
    (V H : E →L[ℝ] E →L[ℝ] ℝ) : (E × E) →L[ℝ] E × E :=
  let fst := ContinuousLinearMap.fst ℝ E E
  let snd := ContinuousLinearMap.snd ℝ E E
  (snd - C.comp fst).prod (B.comp (V.comp fst - H.comp snd) - C.comp snd)

theorem covariantLinearPhaseOperator_apply (B : (E →L[ℝ] ℝ) →L[ℝ] E) (C : E →L[ℝ] E)
    (V H : E →L[ℝ] E →L[ℝ] ℝ) (y p : E) :
    covariantLinearPhaseOperator B C V H (y, p) = (p - C y, B (V y - H p) - C p) := rfl

theorem covariantLinearPhaseOperator_pair (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ η w, G (B η) w = η w)
    (C : E →L[ℝ] E) (V H : E →L[ℝ] E →L[ℝ] ℝ) (y p w : E) :
    G ((covariantLinearPhaseOperator B C V H (y, p)).2 + C p) w = V y w - H p w := by
  rw [covariantLinearPhaseOperator_apply, sub_add_cancel, hB]
  rfl

theorem covariantLinearPhaseOperator_eq_of_pair (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, B (G v) = v)
    (C : E →L[ℝ] E) (V H : E →L[ℝ] E →L[ℝ] ℝ) (y p dy dp : E)
    (hdy : dy = p - C y) (hdp : ∀ w, G (dp + C p) w = V y w - H p w) :
    (dy, dp) = covariantLinearPhaseOperator B C V H (y, p) := by
  have hcov : G (dp + C p) = V y - H p := by ext w; exact hdp w
  have h := congrArg B hcov
  rw [hB] at h
  rw [covariantLinearPhaseOperator_apply]
  exact Prod.ext hdy (eq_sub_iff_add_eq.mpr h)

def jacobiPhaseOperator (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H Ric : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A : E) : (E × E) →L[ℝ] E × E :=
  covariantLinearPhaseOperator B (Γ A) (jacobiPotentialCovector R H N s A) ((4 * s) • Ric)

theorem jacobiPhaseOperator_apply (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H Ric : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A y p : E) :
    jacobiPhaseOperator B Γ R H Ric N s A (y, p) =
      (p - Γ A y, B (jacobiPotentialCovector R H N s A y - (4 * s) • Ric p) - Γ A p) := rfl

theorem jacobiPhaseOperator_residual (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ η w, G (B η) w = η w)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H Ric : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A y p w : E) :
    G ((jacobiPhaseOperator B Γ R H Ric N s A (y, p)).2 + Γ A p) w +
      R y A w A - 2 * s * (N A y w + N y A w - N w A y) -
      2 * s ^ 2 * H y w + 4 * s * N y A w + 4 * s * Ric p w = 0 := by
  rw [jacobiPhaseOperator_apply, sub_add_cancel, hB]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, jacobiPotentialCovector_apply]
  ring

theorem jacobiPhaseOperator_eq_of_residual (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, B (G v) = v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H Ric : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (s : ℝ) (A y p dy dp : E) (hdy : dy = p - Γ A y)
    (hres : ∀ w, G (dp + Γ A p) w + R y A w A -
      2 * s * (N A y w + N y A w - N w A y) - 2 * s ^ 2 * H y w +
        4 * s * N y A w + 4 * s * Ric p w = 0) :
    (dy, dp) = jacobiPhaseOperator B Γ R H Ric N s A (y, p) := by
  have hcov : G (dp + Γ A p) = jacobiPotentialCovector R H N s A y - (4 * s) • Ric p := by
    ext w
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, jacobiPotentialCovector_apply]
    linarith [hres w]
  have hdp := congrArg B hcov
  rw [hB] at hdp
  rw [jacobiPhaseOperator_apply]
  exact Prod.ext hdy (eq_sub_iff_add_eq.mpr hdp)

def jacobiChristoffelOperator (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) B).comp
    ((1 / 2 : ℝ) • (DG + DG.flip -
      ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap).comp
        DG.flip))

theorem jacobiChristoffelOperator_apply (B : (E →L[ℝ] ℝ) →L[ℝ] E)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    jacobiChristoffelOperator B DG v w =
      B ((1 / 2 : ℝ) • (DG v w + DG w v - (DG.flip v).flip w)) := rfl

variable [FiniteDimensional ℝ E]

theorem covariantLinearPhaseOperator_contDiffOn {S : Set ℝ}
    {B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {C : ℝ → E →L[ℝ] E}
    {V H : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B S) (hC : ContDiffOn ℝ ∞ C S)
    (hV : ContDiffOn ℝ ∞ V S) (hH : ContDiffOn ℝ ∞ H S) :
    ContDiffOn ℝ ∞ (fun s ↦ covariantLinearPhaseOperator (B s) (C s) (V s) (H s)) S := by
  apply contDiffOn_clm_apply.mpr
  rintro ⟨y, p⟩
  simp only [covariantLinearPhaseOperator_apply]
  exact (contDiffOn_const.sub (hC.clm_apply contDiffOn_const)).prodMk
    ((hB.clm_apply ((hV.clm_apply contDiffOn_const).sub (hH.clm_apply contDiffOn_const))).sub
      (hC.clm_apply contDiffOn_const))

theorem jacobiPotentialCovector_contDiffOn {C : Set ℝ}
    {R : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {H : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {N : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {A : ℝ → E} (hR : ContDiffOn ℝ ∞ R C) (hH : ContDiffOn ℝ ∞ H C)
    (hN : ContDiffOn ℝ ∞ N C) (hA : ContDiffOn ℝ ∞ A C) :
    ContDiffOn ℝ ∞ (fun s ↦ jacobiPotentialCovector (R s) (H s) (N s) s (A s)) C := by
  apply contDiffOn_clm_apply.mpr
  intro y
  apply contDiffOn_clm_apply.mpr
  intro w
  simp only [jacobiPotentialCovector_apply]
  exact ((((hR.clm_apply contDiffOn_const).clm_apply hA).clm_apply contDiffOn_const).clm_apply hA).neg.add
    ((contDiffOn_const.mul contDiffOn_id).mul
      ((((hN.clm_apply hA).clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
        (((hN.clm_apply contDiffOn_const).clm_apply hA).clm_apply contDiffOn_const) |>.sub
          (((hN.clm_apply contDiffOn_const).clm_apply hA).clm_apply contDiffOn_const))) |>.add
    ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul
      ((hH.clm_apply contDiffOn_const).clm_apply contDiffOn_const)) |>.sub
    ((contDiffOn_const.mul contDiffOn_id).mul
      (((hN.clm_apply contDiffOn_const).clm_apply hA).clm_apply contDiffOn_const))

theorem jacobiPhaseOperator_contDiffOn {C : Set ℝ}
    {B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E} {Γ : ℝ → E →L[ℝ] E →L[ℝ] E}
    {R : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    {H Ric : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {N : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {A : ℝ → E}
    (hB : ContDiffOn ℝ ∞ B C) (hΓ : ContDiffOn ℝ ∞ Γ C)
    (hR : ContDiffOn ℝ ∞ R C) (hH : ContDiffOn ℝ ∞ H C)
    (hRic : ContDiffOn ℝ ∞ Ric C) (hN : ContDiffOn ℝ ∞ N C)
    (hA : ContDiffOn ℝ ∞ A C) :
    ContDiffOn ℝ ∞ (fun s ↦ jacobiPhaseOperator (B s) (Γ s) (R s) (H s) (Ric s) (N s) s (A s)) C := by
  apply contDiffOn_clm_apply.mpr
  rintro ⟨y, p⟩
  simp only [jacobiPhaseOperator_apply]
  have hV := jacobiPotentialCovector_contDiffOn hR hH hN hA
  exact (contDiffOn_const.sub ((hΓ.clm_apply hA).clm_apply contDiffOn_const)).prodMk
    ((hB.clm_apply ((hV.clm_apply contDiffOn_const).sub
      ((contDiffOn_const.mul contDiffOn_id).smul (hRic.clm_apply contDiffOn_const)))).sub
        ((hΓ.clm_apply hA).clm_apply contDiffOn_const))

theorem jacobiChristoffelOperator_contDiffOn {C : Set ℝ}
    {B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E}
    {DG : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B C) (hDG : ContDiffOn ℝ ∞ DG C) :
    ContDiffOn ℝ ∞ (fun s ↦ jacobiChristoffelOperator (B s) (DG s)) C := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  simp only [jacobiChristoffelOperator_apply]
  apply hB.clm_apply
  apply contDiffOn_clm_apply.mpr
  intro z
  change ContDiffOn ℝ ∞ (fun s ↦ (1 / 2 : ℝ) *
    (DG s v w z + DG s w v z - DG s z v w)) C
  exact contDiffOn_const.mul
    ((((hDG.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
      (((hDG.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const) |>.sub
        (((hDG.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const))

variable [CompleteSpace E]

theorem exists_covariant_linear_phase_solution {a b t₀ : ℝ}
    (B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E) (C : ℝ → E →L[ℝ] E)
    (V H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b)) (hC : ContDiffOn ℝ ∞ C (Icc a b))
    (hV : ContDiffOn ℝ ∞ V (Icc a b)) (hH : ContDiffOn ℝ ∞ H (Icc a b))
    (ht₀ : t₀ ∈ Icc a b) (z₀ : E × E) :
    ∃ z : ℝ → E × E, z t₀ = z₀ ∧ ContDiffOn ℝ ∞ z (Icc a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt z
        (covariantLinearPhaseOperator (B s) (C s) (V s) (H s) (z s)) (Icc a b) s := by
  let L := fun s ↦ covariantLinearPhaseOperator (B s) (C s) (V s) (H s)
  have hL : ContDiffOn ℝ ∞ L (Icc a b) :=
    covariantLinearPhaseOperator_contDiffOn hB hC hV hH
  obtain ⟨z, hz₀, hzd⟩ := exists_linear_interval_solution L hL.continuousOn ht₀ z₀
  exact ⟨z, hz₀, linear_interval_solution_contDiffOn L hL hzd, hzd⟩

theorem covariant_linear_phase_unique {a b t₀ : ℝ}
    (B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E) (C : ℝ → E →L[ℝ] E)
    (V H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Icc a b)) (hC : ContDiffOn ℝ ∞ C (Icc a b))
    (hV : ContDiffOn ℝ ∞ V (Icc a b)) (hH : ContDiffOn ℝ ∞ H (Icc a b))
    (ht₀ : t₀ ∈ Icc a b) {f g : ℝ → E × E}
    (hf : ∀ s ∈ Icc a b, HasDerivWithinAt f
      (covariantLinearPhaseOperator (B s) (C s) (V s) (H s) (f s)) (Icc a b) s)
    (hg : ∀ s ∈ Icc a b, HasDerivWithinAt g
      (covariantLinearPhaseOperator (B s) (C s) (V s) (H s) (g s)) (Icc a b) s)
    (heq : f t₀ = g t₀) : EqOn f g (Icc a b) :=
  linear_interval_solution_unique _
    (covariantLinearPhaseOperator_contDiffOn hB hC hV hH).continuousOn ht₀ hf hg heq

theorem exists_jacobi_phase_solution {a b t₀ : ℝ}
    (B : ℝ → (E →L[ℝ] ℝ) →L[ℝ] E) (Γ : ℝ → E →L[ℝ] E →L[ℝ] E)
    (R : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (H Ric : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (N : ℝ → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (A : ℝ → E)
    (hB : ContDiffOn ℝ ∞ B (Icc a b)) (hΓ : ContDiffOn ℝ ∞ Γ (Icc a b))
    (hR : ContDiffOn ℝ ∞ R (Icc a b)) (hH : ContDiffOn ℝ ∞ H (Icc a b))
    (hRic : ContDiffOn ℝ ∞ Ric (Icc a b)) (hN : ContDiffOn ℝ ∞ N (Icc a b))
    (hA : ContDiffOn ℝ ∞ A (Icc a b)) (ht₀ : t₀ ∈ Icc a b) (z₀ : E × E) :
    ∃ z : ℝ → E × E, z t₀ = z₀ ∧ ContDiffOn ℝ ∞ z (Icc a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt z
        (jacobiPhaseOperator (B s) (Γ s) (R s) (H s) (Ric s) (N s) s (A s) (z s))
        (Icc a b) s := by
  let L := fun s ↦ jacobiPhaseOperator (B s) (Γ s) (R s) (H s) (Ric s) (N s) s (A s)
  have hL : ContDiffOn ℝ ∞ L (Icc a b) :=
    jacobiPhaseOperator_contDiffOn hB hΓ hR hH hRic hN hA
  obtain ⟨z, hz₀, hzd⟩ := exists_linear_interval_solution L hL.continuousOn ht₀ z₀
  exact ⟨z, hz₀, linear_interval_solution_contDiffOn L hL hzd, hzd⟩

end PoincareConjecture.M08
