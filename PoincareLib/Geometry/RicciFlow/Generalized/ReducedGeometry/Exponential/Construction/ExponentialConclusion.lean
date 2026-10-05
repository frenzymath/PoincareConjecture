import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialFamily
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Action.ActionDifferential
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.JointMap
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StrictPrefix

/-!
# The full generalized exponential conclusion

Morgan-Tian Definition 6.17, Lemmas 6.18--6.22, Definition 6.25
and Propositions 6.28--6.30, pp. 113-119. The actual family, action
differential, full stable sets, joint inverse and strict-prefix
theorem supply every field of the frozen exponential conclusion.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- The complete frozen generalized exponential conclusion, retaining
actual paths, differentials, Jacobi fields, stable carriers and joint
inverse data, Definition 6.17 through Proposition 6.30, pp. 113-119. -/
theorem exponentialConclusion
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14ExponentialConclusion G :=
  { family := fun _ _ hbase => ⟨exponentialFamily hM04 hM12 hbase⟩
    action_differential := actionDifferentialStatement hCoordinates hM04 hM12
    differential_mfderiv := fun _ _ E => E.differential_pointwise_mfderiv
    path_euler_transport := fun _ _ E => E.path_euler
    action_transport := fun _ _ E => E.action_eq
    reduced_length_transport := fun _ _ E => E.reduced_length_eq
    global_action_transport := fun _ _ E => E.action_global_eq
    global_reduced_length_transport := fun _ _ E => E.reduced_length_global_eq
    positive_survival := fun _ _ E => E.positive_survival_iff
    initial_value_uniqueness := fun _ _ E => E.initial_value_agreement
    stable := fun _ _ _ _ hτ E hsurv => stableSet_nonempty E hτ hsurv
    joint_domain := fun _ _ _ => rfl
    joint_map := fun _ _ E => jointMapData_nonempty E
    strict_prefix := fun _ _ _ _ E H₀ => strictPrefix hCoordinates hM04 hM12 E H₀
    euler_transport := fun _ _ E => E.square_euler
    jacobi_transport := fun _ _ E => E.jacobi_equation }

end PoincareMT.M14
