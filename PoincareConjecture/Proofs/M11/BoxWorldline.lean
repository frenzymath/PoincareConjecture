import PoincareConjecture.Proofs.M11.WorldlineRestriction
import PoincareConjecture.Proofs.M11.SpacetimeGeometry
import PoincareConjecture.Proofs.M11.BoxInverseDifferential
import PoincareConjecture.Proofs.M11.IntervalConstant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]

theorem worldline_box_inverse_smooth (A : AdaptedMetricAtlas n X) (K : SpacetimeInterval)
    (γ : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval K))
    (b : A.box_index) (hb : ∀ t, γ.curve t ∈ (boxHomeomorph (A.box b)).target) :
    letI := intervalChartedSpace (A.box b).interval
    ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞ ((boxHomeomorph (A.box b)).symm ∘ γ.curve) := by
  let := intervalChartedSpace K
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  intro t
  exact ((box_inverse_smooth A b).contMDiffAt
    ((boxHomeomorph (A.box b)).open_target.mem_nhds (hb t))).comp t (γ.smooth t)

theorem worldline_box_inverse_derivative (A : AdaptedMetricAtlas n X) (K : SpacetimeInterval)
    (γ : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval K))
    (b : A.box_index) (t : (smoothInterval K).Point)
    (ht : γ.curve t ∈ (boxHomeomorph (A.box b)).target) :
    letI := intervalChartedSpace (A.box b).interval
    mfderiv (𝓡∂ 1) (spacetimeModel n) ((boxHomeomorph (A.box b)).symm ∘ γ.curve) t
      ((smoothInterval K).positiveTangent t) =
        boxPositiveTangent (A.box b) ((boxHomeomorph (A.box b)).symm (γ.curve t)) := by
  let := intervalChartedSpace K
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  let q := (boxHomeomorph (A.box b)).symm (γ.curve t)
  have hi := (box_inverse_smooth A b).contMDiffAt
    ((boxHomeomorph (A.box b)).open_target.mem_nhds ht)
  rw [mfderiv_comp_apply t (hi.mdifferentiableAt (by simp))
    ((γ.smooth t).mdifferentiableAt (by simp)), γ.derivative_eq,
    ← box_inverse_mfderiv A b (γ.curve t) ht]
  have hv := adaptedTimeVector_box A b q
  rw [boxHomeomorph_right_inv (A.box b) ht] at hv
  change (boxTangentEquiv A b q).symm (adaptedTimeVector A (γ.curve t)) = _
  rw [hv]
  exact (boxTangentEquiv A b q).symm_apply_apply (boxPositiveTangent (A.box b) q)

theorem worldline_box_spatial_constant (A : AdaptedMetricAtlas n X) (K : SpacetimeInterval)
    (γ : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval K))
    (b : A.box_index) (hb : ∀ t, γ.curve t ∈ (boxHomeomorph (A.box b)).target)
    (s t : (smoothInterval K).Point) :
    ((boxHomeomorph (A.box b)).symm (γ.curve s)).2 =
      ((boxHomeomorph (A.box b)).symm (γ.curve t)).2 := by
  let := intervalChartedSpace K
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  let f := (boxHomeomorph (A.box b)).symm ∘ γ.curve
  have hf := worldline_box_inverse_smooth A K γ b hb
  apply Subtype.ext
  apply interval_constant_of_derivative_zero K ((box_space_smooth (A.box b)).comp hf)
  intro r
  rw [mfderiv_comp_apply r (((box_space_smooth (A.box b)) (f r)).mdifferentiableAt (by simp))
    ((hf r).mdifferentiableAt (by simp)), worldline_box_inverse_derivative A K γ b r (hb r),
    box_space_mfderiv]
  rfl

end PoincareConjecture.Proofs.M11
