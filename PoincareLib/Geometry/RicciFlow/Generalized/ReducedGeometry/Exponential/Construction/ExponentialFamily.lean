import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialJacobiDerivative
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialActionTime
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialTangent
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Equation.SquareEulerReverse

/-!
# The complete actual maximal square-root exponential family

Morgan-Tian Definition 6.17, Lemmas 6.18--6.19 and Claim 6.20,
pp. 113-114. The actual survival domain, coherent IVP paths, actual
action, genuine initial-vector differential and normalized actual
Jacobi fields supply every field of the frozen exponential record.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The actual maximal square-root IVP, including its true action and
its actual differential represented by normalized Jacobi fields,
supplies the full frozen exponential family, Definition 6.17,
Lemmas 6.18--6.19 and Claim 6.20, pp. 113-114. -/
noncomputable def exponentialFamily
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) : M14ExponentialFamily G T x := by
  let P (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ initialValueDomain G T x)
      (hpos : 0 < s) :=
    selectedInitialValuePath ⟨hpos, (initialValueDomain_positive_iff hpos).mp hs⟩
  let EP (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ initialValueDomain G T x)
      (hpos : 0 < s) :=
    Classical.choice (exists_backwardVelocity_extension_of_square (P Z s hs hpos).square_path)
  let Q (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ initialValueDomain G T x)
      (hpos : 0 < s) (W : G.Horizontal x) :=
    initialValuePath_differentialData hM04 hM12 (P Z s hs hpos) W
  have hdiff (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ initialValueDomain G T x)
      (hpos : 0 < s) (W : G.Horizontal x) :
      ∃ hEq : (P Z s hs hpos).square_path.curve s = initialValueCurve G T x Z s,
        initialValueDifferential G T x Z s W = hEq ▸ (Q Z s hs hpos W).field s := by
    have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
      simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
        (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
    let hEq := (initialValueCurve_eqOn_square hM04 hM12 (P Z s hs hpos) hsC).symm
    refine ⟨hEq, eq_of_heq ?_⟩
    exact (initialValuePath_differentialField_heq hM04 hM12 (P Z s hs hpos) W hsC).symm.trans
      (eqRec_heq hEq ((Q Z s hs hpos W).field s)).symm
  exact {
    base_time := hbase
    domain := initialValueDomain G T x
    domain_admissible := initialValueDomain_admissible hbase
    domain_relative_open := initialValueDomain_relative_open hM04 hM12 hbase
    domain_zero := initialValueDomain_zero
    gamma := initialValueCurve G T x
    gamma_at_zero := initialValueCurve_zero
    family_smooth := initialValueCurve_family_smooth hM04 hM12 hbase
    joint_continuous := initialValueCurve_joint_continuous hM04 hM12 hbase
    clock := fun _ _ hs => initialValueCurve_clock hbase hs
    path := fun Z s hs hpos => (P Z s hs hpos).path
    path_coherent := fun Z s hs hpos _ hr =>
      initialValueCurve_eqOn_path hM04 hM12 (P Z s hs hpos) hr
    path_extension := EP
    path_euler := fun Z s hs hpos =>
      eulerEquation_of_squareRootEuler hM12 (P Z s hs hpos).square_path
        (P Z s hs hpos).extension (P Z s hs hpos).euler (EP Z s hs hpos)
    positive_survival_iff := fun _ _ hpos => initialValueDomain_positive_iff hpos
    initial_value_agreement := fun _ _ _ _ A => initialValueCurve_eqOn_path hM04 hM12 A
    square_path := fun Z s hs hpos => (P Z s hs hpos).square_path
    square_extension := fun Z s hs hpos => (P Z s hs hpos).extension
    square_euler := fun Z s hs hpos => (P Z s hs hpos).euler
    square_initial_velocity := fun Z s hs hpos => (P Z s hs hpos).initial_velocity
    action := initialValueAction G T x
    action_eq := fun Z s hs hpos => initialValueAction_eq_of_path hM04 hM12 hpos (P Z s hs hpos)
    action_global_eq := fun Z s hs hpos hmin =>
      (initialValueAction_eq_of_path hM04 hM12 hpos (P Z s hs hpos)).trans
        (action_eq_actionValue_of_minimizing (P Z s hs hpos).path hmin)
    action_time_derivative := fun Z s hs hpos =>
      initialValueAction_hasDerivWithinAt hM04 hM12 hpos (P Z s hs hpos)
    reduced_length := fun Z s => initialValueAction G T x Z s / (2 * s)
    reduced_length_eq := fun _ _ _ _ => rfl
    reduced_length_global_eq := fun Z s hs hpos hmin => by
      rw [M14ReducedLengthValue, Real.sqrt_sq hpos.le,
        initialValueAction_eq_of_path hM04 hM12 hpos (P Z s hs hpos),
        action_eq_actionValue_of_minimizing (P Z s hs hpos).path hmin]
    initial_derivative := fun Z s hs hpos => initialValuePath_initial_derivative (P Z s hs hpos)
    differential := fun Z s _ => initialValueDifferential G T x Z s
    ambient_differential := fun Z s _ =>
      M14InitialVectorDerivative G (initialValueCurve G T x) s Z
    ambient_differential_eq := fun _ _ _ => rfl
    differential_pointwise_mfderiv := fun _ _ hs W =>
      initialValueDifferential_val hM04 hM12 hbase hs W
    differential_val_eq := fun _ _ hs W => initialValueDifferential_val hM04 hM12 hbase hs W
    differential_jacobi_map := fun Z s hs hpos W => ⟨Q Z s hs hpos W, hdiff Z s hs hpos W⟩
    jacobi_path := fun Z s hs hpos W => ⟨Q Z s hs hpos W,
      initialValuePath_differentialField_zero hM04 hM12 (P Z s hs hpos) W,
      initialValuePath_differential_initialDerivative hM04 hM12 (P Z s hs hpos) W⟩
    jacobi_equation := fun Z s hs hpos W _ hr V =>
      initialValuePath_differential_jacobi hM04 hM12 (P Z s hs hpos) W hr V
    differential_jacobi := hdiff
    jacobi_initial_zero := fun Z s hs hpos W =>
      initialValuePath_differentialField_zero hM04 hM12 (P Z s hs hpos) W
    jacobi_initial_derivative := fun Z s hs hpos W =>
      initialValuePath_differential_initialDerivative hM04 hM12 (P Z s hs hpos) W
    maximal_lifetime := initialValueDomain_ordConnected }

end PoincareMT.M14
