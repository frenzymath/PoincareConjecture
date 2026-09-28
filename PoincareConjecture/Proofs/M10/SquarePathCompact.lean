import PoincareConjecture.Proofs.M10.SquarePathModulus
import PoincareConjecture.Proofs.M10.ClippedCurves
import PoincareConjecture.Proofs.M10.ConnectedEMetric

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem exists_compact_square_endpoints
    (G : LExponentialGeometry F T τmax p) (hcomplete : MetricComplete (F.metric T))
    {ι : Type v} (Z : ι → TangentSpace (𝓡 n) p) (τ : ι → ℝ) {b K : ℝ}
    (hb : 0 < b) (hbmax : b < τmax) (hτ : ∀ i, 0 < τ i) (hτb : ∀ i, τ i ≤ b)
    (hK : 0 ≤ K)
    (henergy : ∀ i, (∫ s in 0..Real.sqrt (τ i), terminalSquareEnergy G (Z i) s) ≤ K) :
    ∃ C : Set M, IsCompact C ∧ ∀ i, G.gamma (Z i) (τ i) ∈ C := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
      fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : CompleteSpace M := hcomplete
  let : MetricSpace M := EMetricSpace.toMetricSpace edist_ne_top_of_preconnected
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡 n)
  have hmod (i : ι) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c)
      (hc : c ≤ Real.sqrt (τ i)) :
      dist (G.squareFamily (Z i) a) (G.squareFamily (Z i) c) ≤
        Real.sqrt (K * (c - a)) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp
    rw [← edist_dist]
    exact edist_squareFamily_le_of_energy G (Z i) (hτ i) ((hτb i).trans_lt hbmax)
      (henergy i) ha hac hc
  obtain ⟨C, hC, hend⟩ := exists_compact_clipped_range
    (γ := fun i ↦ G.squareFamily (Z i)) (S := fun i ↦ Real.sqrt (τ i))
    (Real.sqrt_nonneg b) (fun i ↦ Real.sqrt_nonneg (τ i))
    (fun i ↦ Real.sqrt_le_sqrt (hτb i)) hK hmod p (by
      intro i
      rw [G.square_agrees (Z i) 0 ⟨le_rfl, Real.sqrt_pos.mpr (hb.trans hbmax)⟩]
      simpa using G.gamma_at_zero (Z i))
  refine ⟨C, hC, fun i ↦ ?_⟩
  have hi := hend i
  rw [G.square_agrees (Z i) (Real.sqrt (τ i))
    ⟨Real.sqrt_nonneg _, Real.sqrt_lt_sqrt (hτ i).le ((hτb i).trans_lt hbmax)⟩,
    Real.sq_sqrt (hτ i).le] at hi
  exact hi

end PoincareConjecture.M10
