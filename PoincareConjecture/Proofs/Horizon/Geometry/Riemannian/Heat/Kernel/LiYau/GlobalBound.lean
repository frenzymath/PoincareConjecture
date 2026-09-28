import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DistanceBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Distance








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData



theorem liYau_bound_of_ricci_lower
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric (m + 1) M} (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) {t : ℝ} (ht : 0 < t) (x : M) :
    g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
        (D.gradient (fun y => Real.log (u (t, y))) x) -
      2 * deriv (fun s => Real.log (u (s, x))) t ≤
      4 * ((m + 1 : ℕ) : ℝ) / t + 4 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * K) := by
  let : ConnectedSpace M := ⟨⟨x⟩⟩
  have hsupport := g.exists_distance_laplacian_upper_support D hm hcomplete
    (Real.sqrt_nonneg K) (by simpa only [Real.sq_sqrt hK] using hRic)
  exact D.liYau_bound_of_distance_upper_supports (by omega) hcomplete
    (mul_nonneg (Nat.cast_nonneg _) hK) (Nat.cast_nonneg m) (Real.sqrt_nonneg K)
    (by simpa only [neg_mul] using hRic) hsupport hu hpos hheat ht x

end PoincareConjecture.LeviCivitaData
