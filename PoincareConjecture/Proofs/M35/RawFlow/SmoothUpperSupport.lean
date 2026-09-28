import PoincareConjecture.Proofs.M35.RawFlow.QuadraticJet
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

theorem exists_smooth_quadratic_upper_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) {η : ℝ} (hη : 0 < η) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧ q x = f x ∧
      (∀ᶠ y in 𝓝 x, f y ≤ q y) ∧ fderiv ℝ q x = fderiv ℝ f x ∧
      ∀ v w, fderiv ℝ (fderiv ℝ q) x v w =
        fderiv ℝ (fderiv ℝ f) x v w + 2 * η * inner ℝ v w := by
  let B := fderiv ℝ (fderiv ℝ f) x
  let I : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hI (v w : E) : I v w = inner ℝ v w := rfl
  let A := B + (2 * η) • I
  let q := quadraticJet (f x) (fderiv ℝ f x) A x
  have hB : ∀ v w, B v w = B w v := hf.isSymmSndFDerivAt (by simp)
  have hA : ∀ v w, A v w = A w v := by
    intro v w
    simp only [A, add_apply, smul_apply, smul_eq_mul, hI]
    rw [hB, real_inner_comm v w]
  have hq : ContDiff ℝ ∞ q := quadraticJet_contDiff _ _ _ _
  refine ⟨q, hq, quadraticJet_self _ _ _ _, ?_, ?_, ?_⟩
  · have hrem := (quadraticJet_remainder_isLittleO hf).bound hη
    filter_upwards [hrem] with y hy
    have he : q y = quadraticJet (f x) (fderiv ℝ f x) B x y + η * ‖y - x‖ ^ 2 := by
      simp only [q, quadraticJet, A, add_apply, smul_apply, smul_eq_mul,
        hI, real_inner_self_eq_norm_sq]
      ring
    rw [he]
    have hh := (le_abs_self _).trans hy
    simpa only [B, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y - x‖), add_comm] using
      (sub_le_iff_le_add.mp hh)
  · rw [show q = quadraticJet (f x) (fderiv ℝ f x) A x from rfl,
      quadraticJet_fderiv _ _ _ hA]
    simp
  · intro v w
    rw [show q = quadraticJet (f x) (fderiv ℝ f x) A x from rfl,
      quadraticJet_second_fderiv _ _ _ hA]
    rfl

theorem exists_smooth_upper_support_laplacian {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ q ∧ q x = f x ∧
      (∀ᶠ y in 𝓝 x, f y ≤ q y) ∧ D.laplacian q x ≤ D.laplacian f x + δ := by
  let e : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → EuclideanSpace ℝ (Fin n) :=
    g.orthonormalBasis x
  let H := ∑ i, ‖e i‖ ^ 2
  have hH : 0 ≤ H := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let η := δ / (2 * (H + 1))
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨q, hq, htouch, hupper, hfirst, hsecond⟩ :=
    exists_smooth_quadratic_upper_support
      (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hη
  refine ⟨q, hq, htouch, hupper, ?_⟩
  have hh (v w : EuclideanSpace ℝ (Fin n)) :
      D.hessian q x v w = D.hessian f x v w + 2 * η * inner ℝ v w := by
    rw [D.hessian_eq_fderiv_sub_christoffel hq.contDiffAt,
      D.hessian_eq_fderiv_sub_christoffel hf, hfirst, hsecond]
    ring
  have hlap : D.laplacian q x = D.laplacian f x + 2 * η * H := by
    simp only [LeviCivitaData.laplacian, hh, real_inner_self_eq_norm_sq,
      Finset.sum_add_distrib, ← Finset.mul_sum, H]
    rfl
  have hηeq : 2 * η * (H + 1) = δ := by
    dsimp only [η]
    field_simp
  rw [hlap]
  nlinarith

end PoincareConjecture.M35.Uniqueness
