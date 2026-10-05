import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Escape of shrinking neck centers

Scalar continuity on a compact set bounds the scales of all necks centered
there from below. Consequently any family of actual necks whose scales tend
to zero has centers escaping every compact set. Neither a global curvature
bound nor a sign condition away from the neck centers is required.

Reference: Morgan--Tian, Proposition 2.19, pp. 31--32.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M]
  {g : RiemannianMetric 3 M}

/-- The connection stored by a neck computes the metric's scalar curvature. -/
theorem scalar_center_eq (N : EpsilonNeck g) (D : LeviCivitaData g) :
    N.connection.scalarCurvature N.center = D.scalarCurvature N.center := by
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
  simp_rw [N.connection.curvatureTensor_eq D N.center]

/-- All necks centered in a fixed compact set have a common positive lower
scale bound, even if the ambient manifold is noncompact. -/
theorem exists_scale_lower_bound_on_compact (D : LeviCivitaData g)
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : EpsilonNeck g, N.center ∈ K → ρ ≤ N.scale := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image D.continuous_scalarCurvature.continuousOn
  let C : ℝ := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨C ^ (-1 / 2 : ℝ), Real.rpow_pos_of_pos hC _, ?_⟩
  intro N hN
  have hscalar : 0 < D.scalarCurvature N.center := by
    rw [← N.scalar_center_eq D]
    exact N.scalar_center_pos
  have hbound : D.scalarCurvature N.center ≤ C :=
    (hB (mem_image_of_mem _ hN)).trans (le_max_left _ _)
  rw [N.scale_eq_scalar, N.scalar_center_eq D]
  exact Real.rpow_le_rpow_of_nonpos hscalar hbound (by norm_num)

/-- On a compact ambient manifold the compact-set estimate is global.  This
closes the compact branch before the point-soul ordering argument is used. -/
theorem exists_scale_lower_bound_of_compactSpace
    [CompactSpace M] (D : LeviCivitaData g) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : EpsilonNeck g, ρ ≤ N.scale := by
  obtain ⟨ρ, hρ, hbound⟩ :=
    exists_scale_lower_bound_on_compact D (K := (Set.univ : Set M)) isCompact_univ
  refine ⟨ρ, hρ, ?_⟩
  intro N
  exact hbound N (Set.mem_univ N.center)

/-- Shrinking scales force the actual centers eventually outside every compact
set. The filter form also applies to subsequences and selected neck families. -/
theorem eventually_center_not_mem_compact_of_scale_tendsto_zero
    (D : LeviCivitaData g) {ι : Type*} {l : Filter ι}
    (N : ι → EpsilonNeck g)
    (hscale : Tendsto (fun i => (N i).scale) l (𝓝 0))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ i in l, (N i).center ∉ K := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_scale_lower_bound_on_compact D hK
  filter_upwards [hscale.eventually_lt_const hρ] with i hi
  exact fun hmem => (not_lt_of_ge (hbound (N i) hmem)) hi

/-- Failure of the desired fixed-epsilon lower bound gives a sequence of actual
necks whose scales vanish and whose centers escape every compact set. -/
theorem exists_escaping_neck_sequence_of_no_scale_lower_bound
    (D : LeviCivitaData g) (ε : ℝ)
    (hsmall : ¬ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ N : EpsilonNeck g, N.epsilon = ε → ρ ≤ N.scale) :
    ∃ N : ℕ → EpsilonNeck g,
      (∀ i, (N i).epsilon = ε) ∧
      Tendsto (fun i => (N i).scale) atTop (𝓝 0) ∧
      ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, (N i).center ∉ K := by
  classical
  have hchoice (i : ℕ) : ∃ N : EpsilonNeck g,
      N.epsilon = ε ∧ N.scale < 1 / ((i : ℝ) + 1) := by
    by_contra h
    push Not at h
    apply hsmall
    exact ⟨1 / ((i : ℝ) + 1), by positivity, h⟩
  choose N hε hscale using hchoice
  have htendsto : Tendsto (fun i => (N i).scale) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun i => (N i).scale_pos.le) (fun i => (hscale i).le)
  exact ⟨N, hε, htendsto, fun K hK =>
    eventually_center_not_mem_compact_of_scale_tendsto_zero D N htendsto hK⟩

end PoincareMT.EpsilonNeck
