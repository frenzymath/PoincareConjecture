import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Geometry.OperatorRicci
import PoincareLib.Geometry.RicciFlow.Splitting.NullSectionEnergy
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.HomotheticField

/-!
# A homothetic terminal field forces Ricci flatness on a finite flow

The same smooth field supplies terminal nullity, and the included-time
Ricci evolution forces its covariant derivatives to be null. No ancient
extension or completeness is needed.
Source: Morgan--Tian Proposition 4.22; M28 derivations 110 and 148.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The actual finite-time terminal Ricci tensor vanishes when the
terminal compatible connection has a smooth field with derivative Id.
The field may vanish and the carrier may be incomplete. Derivation 148. -/
theorem terminal_ricci_eq_zero_of_homothetic_field
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (Z : (x : M) → TangentSpace (𝓡 3) x)
    (hZsmooth : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% Z))
    (hZ : ∀ x, ∀ v : TangentSpace (𝓡 3) x, (F.connection b).connection Z x v = v) :
    ∀ x, ∀ v w : TangentSpace (𝓡 3) x, (F.connection b).ricci x v w = 0 := by
  let D := F.connection b
  have hD : D.CurvatureTensorCalculus := P.tensor_calculus 3 M (F.metric b) D
  have hconst : ∀ x, ∀ v : TangentSpace (𝓡 3) x, D.connection Z x v = (1 : ℝ) • v := by
    simpa only [one_smul] using hZ
  have hnull (y : M) : D.ricci y (Z y) (Z y) = 0 := by
    unfold LeviCivitaData.ricci
    apply Finset.sum_eq_zero
    intro i _
    rw [M04.curvatureTensor_swap_last,
      D.curvatureTensor_eq_zero_of_constant_covariantDerivative hD Z hZsmooth 1 hconst,
      neg_zero]
  have hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature := by
    intro t ht x v w
    exact (F.connection t).sectional_nonneg_of_nonnegative_operator_m28 x (hoperator t ht x) v w
  intro x v w
  have h := RicciFlow.Splitting.ricci_connection_eq_zero_of_terminal_null
    P hab F hsec Z (hZsmooth x) (Eventually.of_forall hnull) v w
  simpa only [hZ] using h

/-- A positive terminal scalar contradicts an actual smooth homothetic
field on a finite nonnegatively curved backward flow. Derivation 148. -/
theorem no_positive_terminal_scalar_of_homothetic_field
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (Z : (x : M) → TangentSpace (𝓡 3) x)
    (hZsmooth : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% Z))
    (hZ : ∀ x, ∀ v : TangentSpace (𝓡 3) x, (F.connection b).connection Z x v = v)
    (p : M) (hscalar : 0 < (F.connection b).scalarCurvature p) : False := by
  have hric := terminal_ricci_eq_zero_of_homothetic_field P hab F hoperator Z hZsmooth hZ p
  have hzero : (F.connection b).scalarCurvature p = 0 := by
    unfold LeviCivitaData.scalarCurvature
    exact Finset.sum_eq_zero fun i _ => hric _ _
  exact (ne_of_gt hscalar) hzero

end PoincareMT.M28
