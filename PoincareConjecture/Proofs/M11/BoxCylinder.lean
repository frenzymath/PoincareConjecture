import PoincareConjecture.Proofs.M11.SpacetimeGeometry
import PoincareConjecture.Definitions.M11CompatibleEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]

noncomputable def adaptedBoxCylinder (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    CompatibleSpacetimeCylinder (adaptedSpacetime A)
      (intervalSystem.interval (A.box b).interval) (A.box b).spatial where
  interval_subset := (A.box b).interval_subset
  toSpacetime := (A.box b).toSpacetime
  embedding := (A.box b).openEmbedding.isEmbedding
  time_eq := (A.box b).time_toSpacetime
  worldline_smooth := by
    intro x
    let := intervalChartedSpace (A.box b).interval
    let := adaptedChartedSpace A
    exact (adapted_box_localDiffeomorph A b).contMDiff.comp
      (contMDiff_id.prodMk contMDiff_const)
  worldline_derivative := by
    intro t x
    let := intervalChartedSpace (A.box b).interval
    let := adaptedChartedSpace A
    have h := mfderiv_comp_apply t
      (((adapted_box_localDiffeomorph A b).contMDiff (t, x)).mdifferentiableAt (by simp))
      ((contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞
        (fun s : (smoothInterval (A.box b).interval).Point ↦ (s, x))) t |>.mdifferentiableAt
        (by simp)) ((smoothInterval (A.box b).interval).positiveTangent t)
    simp only [id_eq] at h
    rw [mfderiv_prod_left] at h
    exact h.trans (adaptedTimeVector_box A b (t, x)).symm
  smooth := by
    let := intervalChartedSpace (A.box b).interval
    let := adaptedChartedSpace A
    exact (adapted_box_localDiffeomorph A b).contMDiff
  differential_injective := by
    let := intervalChartedSpace (A.box b).interval
    let := adaptedChartedSpace A
    exact fun p ↦ (boxTangentEquiv A b p).injective

end PoincareConjecture.Proofs.M11
