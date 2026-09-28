import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem exists_compact_coordinate_bounds (g : RiemannianMetric n M) (q : M) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      let c := extChartAt (𝓡 n) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      IsCompact (c.symm '' Metric.closedBall (c q) r) ∧
      ∀ z ∈ Metric.closedBall (c q) r,
        (∀ v : EuclideanSpace ℝ (Fin n),
          g.tangentNorm (c.symm z) (mfderiv (𝓡 n) (𝓡 n) c.symm z v) ≤ C * ‖v‖) ∧
        (∀ w : TangentSpace (𝓡 n) (c.symm z),
          ‖mfderiv (𝓡 n) (𝓡 n) c (c.symm z) w‖ ≤ C * g.tangentNorm (c.symm z) w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let c := extChartAt (𝓡 n) q
  obtain ⟨A, hA, hforward⟩ := eventually_norm_mfderiv_extChartAt_lt (𝓡 n) q
  obtain ⟨B, hB, hinverse⟩ :=
    eventually_norm_mfderivWithin_symm_extChartAt_lt (𝓡 n) q
  have hinverse' : ∀ᶠ z in 𝓝 (c q), ‖mfderiv (𝓡 n) (𝓡 n) c.symm z‖ < B := by
    simpa [c, mfderivWithin_univ] using hinverse
  have hforward' : ∀ᶠ z in 𝓝 (c q),
      ‖mfderiv (𝓡 n) (𝓡 n) c (c.symm z)‖ < A := by
    have hcont : ContinuousAt c.symm (c q) := continuousAt_extChartAt_symm q
    have heq : c.symm (c q) = q := by simp [c]
    have hforward₁ : ∀ᶠ y in 𝓝 (c.symm (c q)),
        ‖mfderiv (𝓡 n) (𝓡 n) c y‖ < A := by
      simpa only [heq] using hforward
    exact hcont.preimage_mem_nhds hforward₁
  have htarget : c.target ∈ 𝓝 (c q) := by
    simpa [c] using extChartAt_target_mem_nhdsWithin (I := 𝓡 n) q
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem htarget (hinverse'.and hforward'))
  refine ⟨r, max A B, hr, lt_max_of_lt_left hA, ?_⟩
  dsimp only
  have hsub : Metric.closedBall (c q) r ⊆ c.target := fun z hz ↦ (hball hz).1
  refine ⟨hsub, (isCompact_closedBall (c q) r).image_of_continuousOn
    ((continuousOn_extChartAt_symm q).mono hsub), ?_⟩
  intro z hz
  obtain ⟨_, hzB, hzA⟩ := hball hz
  constructor
  · intro v
    have h := (mfderiv (𝓡 n) (𝓡 n) c.symm z).le_opNorm v
    have hnorm : ‖mfderiv (𝓡 n) (𝓡 n) c.symm z v‖ =
        g.tangentNorm (c.symm z) (mfderiv (𝓡 n) (𝓡 n) c.symm z v) := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    rw [hnorm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hzB.le.trans (le_max_right A B))
      (norm_nonneg v))
  · intro w
    have h := (mfderiv (𝓡 n) (𝓡 n) c (c.symm z)).le_opNorm w
    have hnorm : ‖w‖ = g.tangentNorm (c.symm z) w := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    rw [hnorm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hzA.le.trans (le_max_left A B))
      (Real.sqrt_nonneg _))

set_option backward.isDefEq.respectTransparency false in


theorem exists_compact_coordinate_ellipticity (g : RiemannianMetric n M) (q : M) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      let c := extChartAt (𝓡 n) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      IsCompact (c.symm '' Metric.closedBall (c q) r) ∧
      ∀ z ∈ Metric.closedBall (c q) r, ∀ v : EuclideanSpace ℝ (Fin n),
        ‖v‖ ≤ C * g.tangentNorm (c.symm z) (mfderiv (𝓡 n) (𝓡 n) c.symm z v) ∧
        g.tangentNorm (c.symm z) (mfderiv (𝓡 n) (𝓡 n) c.symm z v) ≤ C * ‖v‖ := by
  obtain ⟨r, C, hr, hC, htarget, hcompact, hbound⟩ := g.exists_compact_coordinate_bounds q
  refine ⟨r, C, hr, hC, htarget, hcompact, ?_⟩
  intro z hz v
  refine ⟨?_, (hbound z hz).1 v⟩
  have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (htarget hz)
  have hcomp' : (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q)
      ((extChartAt (𝓡 n) q).symm z))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z v) = v := by
    have h := congrArg (fun L => L v) hcomp
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact h
  simpa only [hcomp'] using (hbound z hz).2
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z v)

end PoincareConjecture.RiemannianMetric
