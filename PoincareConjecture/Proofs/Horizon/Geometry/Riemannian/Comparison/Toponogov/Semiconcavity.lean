import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem squared_distance_sub_sq_concave
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {γ : ℝ → M} {a b : ℝ}
    (hγ : g.IsGeodesicOn γ (Icc a b))
    (hspeed : ∀ t ∈ Icc a b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hmin : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ConcaveOn ℝ (Icc a b) (fun t => (g.edist p (γ t)).toReal ^ 2 - t ^ 2) := by
  have hγcont : ContinuousOn γ (Icc a b) := fun t ht =>
    (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t => (g.edist p (γ t)).toReal ^ 2) (Icc a b) :=
    ((g.continuous_toReal_edist p).comp_continuousOn hγcont).pow 2
  suffices h : ConcaveOn ℝ (Icc a b)
      (fun t => (g.edist p (γ t)).toReal ^ 2 - 1 * t ^ 2) by
    simpa only [one_mul] using h
  apply Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support hcont
  intro t ht ε hε
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  by_cases hpx : p = γ t
  · refine ⟨fun s => (s - t) ^ 2, by fun_prop, ?_, ?_, ?_⟩
    · rw [hpx, hmin t htcc t htcc]
      simp
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [hpx, hmin t htcc s ⟨hs.1.le, hs.2.le⟩,
        ENNReal.toReal_ofReal (abs_nonneg _), sq_abs]
      nlinarith
    · have hfirst : deriv (fun s : ℝ => (s - t) ^ 2) =
          (fun s => 2 * (s - t)) := by
        funext s
        convert! (((hasDerivAt_id s).sub_const t).pow 2).deriv using 1
        simp
      have hsecond := (((hasDerivAt_id t).sub_const t).const_mul 2).deriv
      change deriv (fun s => 2 * (s - t)) t = 2 * 1 at hsecond
      rw [hfirst, hsecond]
      linarith
  · obtain ⟨u, hu, htouch, hmajor, hbound⟩ :=
      g.exists_squared_distance_upper_support D hcomplete hsec p hγ htcc hpx hε
    have hs : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 :=
      Real.sqrt_eq_one.mp (hspeed t htcc)
    exact ⟨u, hu, htouch, hmajor, by simpa only [hs] using hbound⟩

end PoincareConjecture.RiemannianMetric
