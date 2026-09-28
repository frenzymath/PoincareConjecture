import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.LevelCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.LocalAtTarget

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem isProperMap_potential (S : GradientShrinkingSolitonData 3 M) :
    IsProperMap S.potential := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨S.potential_C2.continuous, ?_⟩
  intro K hK
  obtain ⟨b, hb⟩ := hK.bddAbove
  exact (S.isCompact_potential_sublevel b).of_isClosed_subset
    (hK.isClosed.preimage S.potential_C2.continuous) (fun x hx => hb hx)

theorem exists_first_variation_potential_level_area
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus) :
    ∃ a : ℝ,
      ContDiffOn ℝ ∞ (S.metric.regularLevelArea S.potential_contMDiff) (Ioi a) ∧
      ∀ t > a, HasDerivAt (S.metric.regularLevelArea S.potential_contMDiff)
        (∫ z,
          let x := openLevelIncl S.potential
            (S.metric.regularDomain S.potential_contMDiff) t z
          let N := S.connection.levelUnitNormal S.potential x
          (1 - S.connection.scalarCurvature x + S.connection.ricci x N N) /
            S.connection.levelQ S.potential x
          ∂S.metric.regularLevelVolume S.potential_contMDiff
            (S.metric.regularDomain S.potential_contMDiff)
            (S.metric.regularDomain_regular S.potential_contMDiff) t) t := by
  obtain ⟨a, ha⟩ := S.exists_regular_potential_superlevel hD
  have hreg : ∀ x, S.potential x ∈ Ioi a →
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0 := fun x hx => ha x hx.le
  obtain ⟨hsmooth, hderiv⟩ := S.connection.first_variation_regularLevelArea
    S.potential_contMDiff isOpen_Ioi (S.isProperMap_potential.restrictPreimage (Ioi a)) hreg
  refine ⟨a, hsmooth, fun t ht => ?_⟩
  apply (hderiv t ht).congr_deriv
  apply integral_congr_ae
  filter_upwards [] with z
  let x := openLevelIncl S.potential
    (S.metric.regularDomain S.potential_contMDiff) t z
  have hQ : 0 < S.connection.levelQ S.potential x :=
    Real.sqrt_pos.mp z.1.2
  rw [S.levelMeanCurvature_eq_soliton_trace x hQ]
  change ((_ / Real.sqrt (S.connection.levelQ S.potential x)) /
    Real.sqrt (S.connection.levelQ S.potential x)) = _
  rw [div_div, ← sq, Real.sq_sqrt hQ.le]

theorem exists_monotone_potential_level_area_of_scalar_le_one
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus) :
    ∃ a : ℝ, ∀ b ≥ a,
      (∀ x : M, b < S.potential x → S.connection.scalarCurvature x ≤ 1) →
      MonotoneOn (S.metric.regularLevelArea S.potential_contMDiff) (Ioi b) := by
  obtain ⟨a, hsmooth, hderiv⟩ := S.exists_first_variation_potential_level_area hD
  refine ⟨a, fun b hab hR => ?_⟩
  apply monotoneOn_of_deriv_nonneg (convex_Ioi b)
    (hsmooth.continuousOn.mono (Ioi_subset_Ioi hab))
  · intro t ht
    have hbt : b < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (hderiv t (hab.trans_lt hbt)).differentiableAt.differentiableWithinAt
  · intro t ht
    have hbt : b < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    rw [(hderiv t (hab.trans_lt hbt)).deriv]
    apply integral_nonneg
    intro z
    dsimp only
    apply div_nonneg
    · have hRx := hR _ (show b < S.potential
          (openLevelIncl S.potential (S.metric.regularDomain S.potential_contMDiff) t z) from
        by
          have hz : S.potential (openLevelIncl S.potential
            (S.metric.regularDomain S.potential_contMDiff) t z) = t := z.2
          rwa [hz])
      let x := openLevelIncl S.potential
        (S.metric.regularDomain S.potential_contMDiff) t z
      have hb := (S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
        (S.nonnegative_curvature x) (S.connection.levelUnitNormal S.potential x)).1
      linarith
    · exact (Real.sqrt_pos.mp z.1.2).le

end PoincareConjecture.GradientShrinkingSolitonData
