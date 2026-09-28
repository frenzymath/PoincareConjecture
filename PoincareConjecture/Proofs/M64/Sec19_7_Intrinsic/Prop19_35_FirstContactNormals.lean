import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FirstContactLocal
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalMetric













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem inverse_height_pairing
    (G : RiemannianMetric 2 AnnulusCoordinates) (z : AnnulusCoordinates)
    (A : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    (hunit : G.inner z (A (0, 1)) (A (0, 1)) = 1)
    (horth : G.inner z (A (0, 1)) (A (1, 0)) = 0)
    (v : AnnulusCoordinates) : (A.symm v).2 = G.inner z (A (0, 1)) v := by
  have hpair (w : ℝ × ℝ) : G.inner z (A (0, 1)) (A w) = w.2 := by
    have hw : w = w.1 • (1, 0) + w.2 • (0, 1) := by ext <;> simp
    conv_lhs => arg 2; rw [hw]
    simp only [map_add, map_smul, horth, hunit, smul_eq_mul, mul_zero, mul_one, zero_add]
  simpa only [A.apply_symm_apply] using (hpair (A.symm v)).symm




theorem m64Intrinsic_first_normal_contact_opposite
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    {S : Set (ℝ × ℝ)} (hS : IsOpen S) {p q : ℝ × ℝ} {R : ℝ}
    (hp : p ∈ S) (hq : q ∈ S) (hpheight : p.2 ∈ Ioc (0 : ℝ) R)
    (hqheight : q.2 ∈ Ioc (0 : ℝ) R) (hne : p ≠ q) (hmeet : u p = u q)
    (hinj : InjOn u (S ∩ {z | 0 < z.2 ∧ z.2 < R}))
    (hip : Function.Injective (fderiv ℝ u p))
    (hiq : Function.Injective (fderiv ℝ u q))
    (hpunit : G.inner (u p) (fderiv ℝ u p (0, 1)) (fderiv ℝ u p (0, 1)) = 1)
    (hqunit : G.inner (u q) (fderiv ℝ u q (0, 1)) (fderiv ℝ u q (0, 1)) = 1)
    (hporth : G.inner (u p) (fderiv ℝ u p (0, 1)) (fderiv ℝ u p (1, 0)) = 0)
    (hqorth : G.inner (u q) (fderiv ℝ u q (0, 1)) (fderiv ℝ u q (1, 0)) = 0) :
    p.2 = R ∧ q.2 = R ∧ fderiv ℝ u p (0, 1) = -fderiv ℝ u q (0, 1) := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ AnnulusCoordinates := by
    simp [AnnulusCoordinates, Module.finrank_prod]
  let A := ((fderiv ℝ u p).toLinearMap.linearEquivOfInjective hip hdim).toContinuousLinearEquiv
  let B := ((fderiv ℝ u q).toLinearMap.linearEquivOfInjective hiq hdim).toContinuousLinearEquiv
  have hA : HasFDerivAt u A.toContinuousLinearMap p :=
    (hu.differentiable (by simp) p).hasFDerivAt
  have hB : HasFDerivAt u B.toContinuousLinearMap q :=
    (hu.differentiable (by simp) q).hasFDerivAt
  have hpR : p.2 = R := by
    by_contra hpR
    apply m64Intrinsic_first_contact_no_common_descent hu hS hp hq hpheight hqheight
      hne hmeet hinj A B hA hB (-B (0, 1)) (Or.inl (lt_of_le_of_ne hpheight.2 hpR))
    right
    simp only [map_neg, B.symm_apply_apply]
    norm_num
  have hqR : q.2 = R := by
    by_contra hqR
    apply m64Intrinsic_first_contact_no_common_descent hu hS hp hq hpheight hqheight
      hne hmeet hinj A B hA hB (-A (0, 1)) _ (Or.inl (lt_of_le_of_ne hqheight.2 hqR))
    right
    simp only [map_neg, A.symm_apply_apply]
    norm_num
  refine ⟨hpR, hqR, ?_⟩
  change A (0, 1) = -B (0, 1)
  by_contra hopp
  have hqunit' : G.inner (u p) (B (0, 1)) (B (0, 1)) = 1 := by
    rw [hmeet]
    exact hqunit
  have hqorth' : G.inner (u p) (B (0, 1)) (B (1, 0)) = 0 := by
    rw [hmeet]
    exact hqorth
  have hsum : A (0, 1) + B (0, 1) ≠ 0 := by
    intro hz
    exact hopp (eq_neg_of_add_eq_zero_left hz)
  have hpos := G.pos (u p) (A (0, 1) + B (0, 1)) hsum
  have hsym : G.inner (u p) (B (0, 1)) (A (0, 1)) =
      G.inner (u p) (A (0, 1)) (B (0, 1)) := G.symm _ _ _
  have hpunit' : G.inner (u p) (A (0, 1)) (A (0, 1)) = 1 := hpunit
  simp only [map_add, add_apply, hpunit', hqunit', hsym] at hpos
  apply m64Intrinsic_first_contact_no_common_descent hu hS hp hq hpheight hqheight
    hne hmeet hinj A B hA hB (-(A (0, 1) + B (0, 1)))
  · right
    rw [inverse_height_pairing G (u p) A hpunit' hporth]
    simp only [map_neg, map_add, hpunit']
    linarith
  · right
    rw [inverse_height_pairing G (u p) B hqunit' hqorth']
    simp only [map_neg, map_add, hqunit', hsym]
    linarith

end PoincareConjecture
