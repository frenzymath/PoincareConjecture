import PoincareConjecture.Definitions.Ch16.CapPersistence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_IntrinsicJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCoefficients

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {t : ℝ} {I : Set ℝ}
  {U : Set (F.slice t).carrier}

noncomputable def capComparisonCoefficients
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : StandardCapSpace → (F.slice t).carrier)
    (s : ℝ) (hs : s ∈ I) :
    StandardCapSpace → StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := by
  intro x
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (e.forward s hs (chart x))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (e.forward s hs (chart x))) := by
    unfold TangentSpace
    infer_instance
  let d : StandardCapSpace →L[ℝ] TangentSpace (𝓡 3) (e.forward s hs (chart x)) :=
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (chart x)).comp
      (mfderiv (𝓡 3) (𝓡 3) chart x)
  exact ((F.parameters.h t)⁻¹ ^ 2) • ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 3) (e.forward s hs (chart x)))
    (F := TangentSpace (𝓡 3) (e.forward s hs (chart x))) (G := ℝ)
    (E' := StandardCapSpace) (F' := StandardCapSpace)
    ((F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).inner
      (e.forward s hs (chart x))) d d

theorem capComparisonCoefficients_apply
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : StandardCapSpace → (F.slice t).carrier)
    (s : ℝ) (hs : s ∈ I) (x v w : StandardCapSpace) :
    capComparisonCoefficients e chart s hs x v w =
      e.pullbackInner s hs (chart x)
        (mfderiv (𝓡 3) (𝓡 3) chart x v)
        (mfderiv (𝓡 3) (𝓡 3) chart x w) := rfl

theorem capComparison_covariant_error_lt
    {S : MaximalStandardCapFlow F.standard_initial} {A eta : ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : StandardCapSpace → (F.slice t).carrier)
    (comparison : SurgeryCapFamilyComparison F S A eta e chart)
    (heta : 0 < eta) (s : ℝ) (hs : s ∈ I) {x : StandardCapSpace}
    (hx : x ∈ F.standard_initial.metric.ball 0 A) {j : ℕ} (hj : j ≤ ⌊eta⁻¹⌋₊) :
    (S.metric s).tensorNorm ((S.connection s).iteratedCovariantTensorDerivative (k := 2)
      (fun y v => capComparisonCoefficients e chart s hs y (v 0) (v 1) -
        (S.metric s).inner y (v 0) (v 1)) j) x < eta := by
  obtain ⟨bound, hbound, _hlifetime, _htime, _himage, hjets⟩ := comparison
  exact metric_covariant_error_lt_of_jet_error (S.metric s) (S.connection s)
    (fun y v => capComparisonCoefficients e chart s hs y (v 0) (v 1)) hj heta
    ((hjets s hs x hx).trans_lt hbound)

theorem capComparison_metric_bounds
    {S : MaximalStandardCapFlow F.standard_initial} {A eta : ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (chart : StandardCapSpace → (F.slice t).carrier)
    (comparison : SurgeryCapFamilyComparison F S A eta e chart)
    (heta : 0 < eta) (s : ℝ) (hs : s ∈ I) {x : StandardCapSpace}
    (hx : x ∈ F.standard_initial.metric.ball 0 A) (v : StandardCapSpace) :
    (1 - eta) * (S.metric s).inner x v v ≤
      capComparisonCoefficients e chart s hs x v v ∧
    capComparisonCoefficients e chart s hs x v v ≤
      (1 + eta) * (S.metric s).inner x v v := by
  obtain ⟨bound, hbound, _hlifetime, _htime, _himage, hjets⟩ := comparison
  exact metric_quadratic_bounds_of_jet_error (S.metric s) (S.connection s)
    (capComparisonCoefficients e chart s hs) heta
    ((hjets s hs x hx).trans_lt hbound) v

theorem capComparisonCoefficients_smooth
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (hU : IsOpen U) {chart : StandardCapSpace → (F.slice t).carrier}
    {V : Set StandardCapSpace} (hV : IsOpen V)
    (hchart : ContMDiffOn (𝓡 3) (𝓡 3) ∞ chart V)
    (hmap : Set.MapsTo chart V U) (s : ℝ) (hs : s ∈ I) :
    ContDiffOn ℝ ∞ (capComparisonCoefficients e chart s hs) V := by
  apply ((M44.cylinderPhysicalCoefficients_smooth e hV hchart hmap s hs).const_smul
    ((F.parameters.h t)⁻¹ ^ 2)).congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact (capComparisonCoefficients_apply e chart s hs x v w).trans
    (M44.cylinderPhysicalCoefficients_normalization e hU hV hchart hmap s hs hx v w).symm

end PoincareConjecture.Proofs.M46
