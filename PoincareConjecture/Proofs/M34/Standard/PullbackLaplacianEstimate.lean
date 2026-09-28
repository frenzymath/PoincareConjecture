import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem abs_laplacian_le_of_hessian_bound (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) {C : ℝ}
    (hbound : ∀ u v : TangentSpace (𝓡 n) x,
      |D.hessian f x u v| ≤ C * g.tangentNorm x u * g.tangentNorm x v) :
    |D.laplacian f x| ≤ (n : ℝ) * C := by
  have hnorm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.tangentNorm x (g.orthonormalBasis x i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Real.sqrt (inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one]
    norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => hbound (g.orthonormalBasis x i) (g.orthonormalBasis x i))
  simp only [hnorm, mul_one] at hsum
  have h := (Finset.abs_sum_le_sum_abs _ _).trans hsum
  simpa [laplacian, TangentSpace] using h




theorem abs_laplacian_le_of_pullback_bounds (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x)) (c : ℝ)
    {a B1 B2 G : ℝ} (ha : 0 < a)
    (hell : ∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v)
    (hfirst : ‖fderiv ℝ (fun y => f (e y) - c) x‖ ≤ B1)
    (hsecond : ‖fderiv ℝ (fderiv ℝ (fun y => f (e y) - c)) x‖ ≤ B2)
    (hmetric : ‖fderiv ℝ (g.pullbackCoefficients e) x‖ ≤ G) :
    |D.laplacian f (e x)| ≤ (n : ℝ) * ((B2 + B1 * ((3 / (2 * a)) * G)) / a) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨h, Dh, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff
    (fun _ _ _ _ => g.symm _ _ _) (fun y hy v hv => by
      have hne : mfderiv (𝓡 n) (𝓡 n) e y v ≠ 0 := by
        intro hz
        apply hv
        apply (hinv y hy).injective
        rw [map_zero]
        convert! hz using 1
      exact g.pos (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) hne)
  have hgerm : h.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  apply D.abs_laplacian_le_of_hessian_bound
  apply Dh.abs_hessian_le_of_elliptic_coordinate_lift D c
    (he.contMDiffAt (hU.mem_nhds hx))
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hinv y hy
  · filter_upwards [hgerm] with y hy
    exact fun v w => congrArg (fun B => B v w) hy
  · exact hf
  · exact ha
  · intro v
    exact (hell v).trans_eq (congrArg (fun B => B v v) (hgerm.eq_of_nhds)).symm
  · exact hfirst
  · exact hsecond
  · rw [hgerm.fderiv_eq]
    exact hmetric

end PoincareConjecture.LeviCivitaData
