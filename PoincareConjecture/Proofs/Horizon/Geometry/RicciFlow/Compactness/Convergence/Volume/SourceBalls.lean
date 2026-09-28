import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_source_ball_subset_image_ball
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t r C : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k : ℕ in atTop,
      (S.flow (G.subsequence k)).ballAt t r ⊆
        (fun x => ((G.embedding k).toFun (t, x)).2) '' G.limitFlow.ballAt t (C * r) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : T3Space G.limitCarrier.carrier := G.limitCarrier.t3Space
  let g := G.limitFlow.metricAt t
  let R := C * r + 1
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact : IsCompact (closure (g.ball G.limitFlow.base R)) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete G.limitFlow.base R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hε : 0 < 1 - C⁻¹ ^ 2 := by
    have hi : 0 < C⁻¹ := inv_pos.mpr hCpos
    have hi1 : C⁻¹ < 1 := (inv_lt_one₀ hCpos).mpr hC
    nlinarith
  filter_upwards [G.eventually_pullback_inner_bounds hcompact ht hε,
    eventually_ge_atTop j] with k hk hjk
  let D := S.carrier (G.subsequence k)
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let : T3Space D.carrier := D.t3Space
  let h := (S.flow (G.subsequence k)).metricAt t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) ht
  have hsource : closure (g.ball G.limitFlow.base R) ⊆ e.source :=
    hj.trans (G.exhaustion_monotone hjk)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source :=
    fun x hx => ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hx).contMDiffWithinAt
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) ht hx
  have hediff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), fun y hy =>
      (hei y hy).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt⟩
  have hbound : ∀ y ∈ e '' closure (g.ball G.limitFlow.base R),
      ∀ v : TangentSpace (𝓡 n) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) ≤ C * h.tangentNorm y v := by
    rintro y ⟨x, hx, rfl⟩ v
    have hy := e.map_source (hsource hx)
    have hback := congrArg (fun L => L v) (hediff.comp_symm_deriv hy)
    simp only [ContinuousLinearMap.comp_apply] at hback
    have hlow := (hk x hx (mfderiv (𝓡 n) (𝓡 n) e.symm (e x) v)).1
    have hleft := e.left_inv (hsource hx)
    have hq : C⁻¹ ^ 2 * g.inner x
        (mfderiv (𝓡 n) (𝓡 n) e.symm (e x) v)
        (mfderiv (𝓡 n) (𝓡 n) e.symm (e x) v) ≤ h.inner (e x) v v := by
      change (1 - (1 - C⁻¹ ^ 2)) * g.inner x _ _ ≤ h.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x _) (mfderiv (𝓡 n) (𝓡 n) e x _) at hlow
      rw [hleft] at hback
      change mfderiv (𝓡 n) (𝓡 n) e x
        (mfderiv (𝓡 n) (𝓡 n) e.symm (e x) v) = v at hback
      rw [hback] at hlow
      simpa only [sub_sub_cancel] using hlow
    have hmult := mul_le_mul_of_nonneg_left hq (sq_nonneg C)
    have hinv : C ^ 2 * C⁻¹ ^ 2 = 1 := by field_simp
    rw [← mul_assoc, hinv, one_mul] at hmult
    rw [hleft]
    change Real.sqrt _ ≤ C * Real.sqrt _
    rw [← Real.sqrt_sq hCpos.le, ← Real.sqrt_mul (sq_nonneg C)]
    exact Real.sqrt_le_sqrt hmult
  have hcover := g.ball_subset_image_ball_of_inverse_tangentNorm_le h e
    G.limitFlow.base (r := r) hR hCpos (by dsimp [R]; linarith) hcompact hsource
    (fun y hy => (hei y hy).of_le (by simp)) hbound
  have hbase : e G.limitFlow.base = (S.flow (G.subsequence k)).base :=
    congrArg Prod.snd (G.base_preserving_at_time hT k ht)
  rw [hbase] at hcover
  change h.ball (S.flow (G.subsequence k)).base r ⊆ e '' g.ball G.limitFlow.base (C * r)
  exact hcover

end PoincareConjecture.PointedGeometricConvergence
