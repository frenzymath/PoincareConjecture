import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.JointSmooth
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.Comparison

/-!
# The exact Proposition 15.2 conclusion

Once the quantitative comparison and older survival are established,
the literal recent coordinate and the proved Ricci time join supply every
field of the contract. The long recent-interval case is closed outright.
Source: Morgan--Tian, Proposition 15.2, printed pp. 353-354.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M45

/-- Exact comparison and actual older duration give the complete glued
neck, including joint smoothness and the unchanged coordinate and inverse.
Source: Proposition 15.2, pp. 353-354. -/
theorem gluingConclusion_of_comparison {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hsmall : beta * epsilon < 1 / 2) (I : M45NeckGluingInput.{u} epsilon beta)
    (hduration : 1 ≤ I.older_duration)
    (hcomparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
      (I.piecewiseTensor I.recent_patch.coordinate)) :
    Nonempty (M45NeckGluingConclusion I) := by
  have hpos : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hprod : beta * epsilon ≤ epsilon := by nlinarith
  have hradius : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hlength : epsilon⁻¹ ≤ (beta * epsilon)⁻¹ := inv_anti₀ hpos hprod
  let patch := I.recent_patch.restrict epsilon⁻¹ hradius hlength
  refine ⟨{
    patch := patch
    coordinate_eq := rfl
    inverse_eq := rfl
    recent_subset := I.recent_patch.restrict_subset epsilon⁻¹ hradius hlength
    older_survival := I.older_survival_of_duration hduration
    comparison := hcomparison
    joint_smooth := ?_
  }⟩
  intro q i j
  apply (I.piecewiseTensor_joint_smooth hpos hsmall q i j).mono
  intro p hp
  refine ⟨?_, hp.2.1, cylinderDomain_mono hpos hprod hp.2.2⟩
  exact ⟨lt_of_le_of_lt (neg_le_neg hduration) hp.1.1, hp.1.2⟩

/-- A recent interval of length at least one already supplies the full
strong-neck conclusion in its own unchanged coordinates. Source:
Proposition 15.2, pp. 353-354. -/
theorem gluingConclusion_of_recent_duration {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hsmall : beta * epsilon < 1 / 2) (I : M45NeckGluingInput.{u} epsilon beta)
    (hduration : 1 ≤ I.recent_duration) :
    Nonempty (M45NeckGluingConclusion I) := by
  exact gluingConclusion_of_comparison hepsilon hbeta hbeta_one hsmall I
    (hduration.trans I.durations_ordered.le)
    (recent_piecewise_comparison hepsilon hbeta hbeta_one I hduration)

/-- Only the short recent-interval case remains in the fixed-epsilon
producer. Source: the first reduction in Proposition 15.2, pp. 353-354. -/
theorem gluingProperty_of_short_inputs {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hsmall : beta * epsilon < 1 / 2)
    (hshort : ∀ I : M45NeckGluingInput.{u} epsilon beta, I.recent_duration < 1 →
      Nonempty (M45NeckGluingConclusion I)) :
    M45NeckGluingProperty.{u} epsilon beta := by
  intro I
  by_cases h : I.recent_duration < 1
  · exact hshort I h
  · exact gluingConclusion_of_recent_duration hepsilon hbeta hbeta_one hsmall I
      (le_of_not_gt h)

end PoincareMT.M45
