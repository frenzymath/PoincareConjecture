import PoincareConjecture.Proofs.M07.Analysis.ODE.Linear.JetBounds
import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.Basic

open Set
open scoped ContDiff
noncomputable section

namespace Poincare.ODE.Jacobi

universe u
variable {P F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : NormedAddCommGroup (F →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

def pairVariationL : (F →L[ℝ] F) →L[ℝ] ((F × F) →L[ℝ] (F × F)) := by
  let L : (F →L[ℝ] F) →ₗ[ℝ] ((F × F) →L[ℝ] (F × F)) :=
    { toFun := fun R => (0 : (F × F) →L[ℝ] F).prod
        (-(R.comp (ContinuousLinearMap.fst ℝ F F)))
      map_add' := by intros; ext z <;> simp [add_comm]
      map_smul' := by intros; ext z <;> simp }
  refine LinearMap.mkContinuous L 1 ?_
  intro R
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) ?_
  intro z
  change ‖(0, -(R z.1))‖ ≤ _
  simp only [Prod.norm_def, norm_zero, norm_neg, max_eq_right (norm_nonneg _)]
  exact (R.le_opNorm z.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg R))

@[simp] theorem pairVariationL_apply (R : F →L[ℝ] F) (z : F × F) :
    pairVariationL R z = (0, -R z.1) := rfl

theorem norm_pairVariationL_le : ‖pairVariationL (F := F)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro R
  rw [one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R) ?_
  intro z
  rw [pairVariationL_apply, Prod.norm_def, norm_zero, norm_neg,
    max_eq_right (norm_nonneg _)]
  exact (R.le_opNorm z.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg R))

theorem pairCoeff_eq_affine [CompleteSpace F] (R : ℝ → F →L[ℝ] F) (t : ℝ) :
    pairCoeff R t = pairCoeff (fun _ => (0 : F →L[ℝ] F)) 0 + pairVariationL (R t) := by
  ext z <;> simp [pairCoeff_apply]

theorem norm_iteratedFDeriv_pairCoeff_le [CompleteSpace F]
    {R : P → F →L[ℝ] F} {p : P} (hR : ContDiffAt ℝ ∞ R p) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => pairCoeff (fun _ => R q) 0) p‖ ≤
      max 1 ‖iteratedFDeriv ℝ k R p‖ := by
  by_cases hk : k = 0
  · subst k
    simp only [norm_iteratedFDeriv_zero]
    exact norm_pairCoeff_le (fun _ => R p) 0
  have hkn : (k : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl k
  have heq : (fun q => pairCoeff (fun _ => R q) 0) =
      (fun _ => pairCoeff (fun _ => (0 : F →L[ℝ] F)) 0) + (pairVariationL (F := F) ∘ R) := by
    funext q; exact pairCoeff_eq_affine (fun _ => R q) 0
  rw [heq, iteratedFDeriv_add_apply (contDiffAt_const.of_le hkn)
    (((pairVariationL (F := F)).contDiff.contDiffAt.comp p hR).of_le hkn)]
  simp only [iteratedFDeriv_const_of_ne hk, Pi.zero_apply, zero_add]
  have h := (pairVariationL (F := F)).norm_iteratedFDeriv_comp_left hR hkn
  have hb := mul_le_mul_of_nonneg_right (norm_pairVariationL_le (F := F))
    (norm_nonneg (iteratedFDeriv ℝ k R p))
  rw [one_mul] at hb
  exact (h.trans hb).trans (le_max_right _ _)

theorem norm_iteratedFDeriv_jacobi_le [CompleteSpace F]
    (n : ℕ) {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    {U : Set P} (hU : IsOpen U) {W : Set (ℝ × P)} (hW : IsOpen W)
    (hUW : Icc a b ×ˢ U ⊆ W)
    {R : ℝ × P → F →L[ℝ] F} {y v : ℝ × P → F} {y₀ v₀ : F}
    (hR : ContDiffOn ℝ ∞ R W) (hy : ContDiffOn ℝ ∞ y W)
    (hv : ContDiffOn ℝ ∞ v W)
    (hyode : ∀ z ∈ W, Poincare.ODE.Parameter.timeFDeriv y z = v z)
    (hvode : ∀ z ∈ W, Poincare.ODE.Parameter.timeFDeriv v z = -(R z) (y z))
    (hyinit : ∀ p ∈ U, y (a, p) = y₀) (hvinit : ∀ p ∈ U, v (a, p) = v₀)
    (hbound : ∀ j ≤ n, ∀ t ∈ Icc a b, ∀ p ∈ U,
      ‖iteratedFDeriv ℝ j (fun q => R (t, q)) p‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) {p : P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ n (fun q => (y (t, q), v (t, q))) p‖ ≤
      max ‖y₀‖ ‖v₀‖ * Real.exp ((2 : ℝ) ^ n * max 1 C * (t - a)) := by
  let A : ℝ × P → (F × F) →L[ℝ] (F × F) :=
    fun z => pairCoeff (fun _ => R z) 0
  have hA : ContDiffOn ℝ ∞ A W := by
    have heq : A = (fun _ => pairCoeff (fun _ => (0 : F →L[ℝ] F)) 0) +
        (pairVariationL (F := F) ∘ R) := by
      funext z; exact pairCoeff_eq_affine (fun _ => R z) 0
    rw [heq]
    exact contDiffOn_const.add ((pairVariationL (F := F)).contDiff.comp_contDiffOn hR)
  have hode : ∀ z ∈ W, Poincare.ODE.Parameter.timeFDeriv (fun w => (y w, v w)) z = A z (y z, v z) := by
    intro z hz
    have hyd := ((hy z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    have hvd := ((hv z hz).contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    change (fderiv ℝ (fun w => (y w, v w)) z) (1, 0) = _
    rw [(hyd.hasFDerivAt.prodMk hvd.hasFDerivAt).fderiv]
    change (Poincare.ODE.Parameter.timeFDeriv y z,
      Poincare.ODE.Parameter.timeFDeriv v z) = _
    rw [hyode z hz, hvode z hz]
    rfl
  have hAbound : ∀ j ≤ n, ∀ s ∈ Icc a b, ∀ q ∈ U,
      ‖iteratedFDeriv ℝ j (fun x => A (s, x)) q‖ ≤ max 1 C := by
    intro j hj s hs q hq
    have hRq : ContDiffAt ℝ ∞ (fun x => R (s, x)) q :=
      ((hR _ (hUW ⟨hs, hq⟩)).contDiffAt (hW.mem_nhds (hUW ⟨hs, hq⟩))).comp q
        (contDiffAt_const.prodMk contDiffAt_id)
    exact (norm_iteratedFDeriv_pairCoeff_le hRq j).trans
      (max_le_max le_rfl (hbound j hj s hs q hq))
  simpa only [Prod.norm_def] using Poincare.ODE.Linear.norm_iteratedFDeriv_linearODE_le
    (y₀ := (y₀, v₀)) n hab (le_trans hC (le_max_right 1 C)) hU hW hUW hA
    (hy.prodMk hv) hode (fun q hq => Prod.ext (hyinit q hq) (hvinit q hq)) hAbound ht hp

end Poincare.ODE.Jacobi
