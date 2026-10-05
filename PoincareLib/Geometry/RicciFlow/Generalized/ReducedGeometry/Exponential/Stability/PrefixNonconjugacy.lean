import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Differential.ExponentialJacobiPhase
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Minimizing.ExponentialMeetingVelocity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialJacobiZero
import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Strict minimizing prefixes are nonconjugate

Morgan-Tian Proposition 6.30, pp. 118-119. The actual smooth broken
cost forces a kernel direction to have zero coordinate phase at the
meeting time. This is the actual Jacobi phase, whose uniqueness and
initial normalization force the initial direction to be zero.
-/

set_option autoImplicit false

open Set
open scoped Manifold

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The actual exponential differential has trivial kernel strictly
before the endpoint of a minimizing branch, Proposition 6.30,
pp. 118-119. No completeness or compactness of the ambient flow is used. -/
theorem exponential_prefix_kernel_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c : ℝ} (hb : (Z, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (hmin : M14IsMinimizing (E.path Z b hb (hc.1.trans hc.2)))
    (hZ : (Z, c) ∈ E.domain) (hker : E.differential Z c hZ W = 0) : W = 0 := by
  obtain ⟨j, V, lift, hV, hcenter, hlift, hright, _⟩ :=
    exists_smooth_gauge_lift G (E.gamma Z c)
  obtain ⟨U, hU, hzero, hsurv, _⟩ :=
    exists_exponentialLine_endpointFamily hM04 hM12 E Z W hb hc j lift hV hlift hright hcenter
  have hcoordinate := exponentialLine_coordinate_deriv_eq_zero E Z W hU hzero hsurv hc hZ hker
    j lift ((hlift _ hcenter).contMDiffAt (hV.mem_nhds hcenter))
  have hvelocity := exponential_meetingVelocity_deriv_eq_zero hCoordinates hM04 hM12 E Z W hb hc
    hmin hZ hker j lift hV hlift hright hcenter
  obtain ⟨hfield, hderiv⟩ := exponentialJacobiField_zero_of_coordinate_phase hM04 hM12 E Z W hb hc
    hU hzero hsurv j lift hV hlift hright hcenter hcoordinate hvelocity
  have hcC : c ∈ M14SqrtParameterInterval 0 (b ^ 2) := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq (hc.1.trans hc.2).le]
    exact ⟨hc.1.le, hc.2.le⟩
  exact initialValuePath_direction_eq_zero_of_phase hM04 hM12
    (exponentialInitialValuePath E Z b hb (hc.1.trans hc.2)) W hcC hfield hderiv

/-- The actual exponential differential is bijective at every strict
positive prefix of a minimizing branch, Proposition 6.30, pp. 118-119. -/
theorem exponential_prefix_differential_bijective
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x)
    {b c : ℝ} (hb : (Z, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (hmin : M14IsMinimizing (E.path Z b hb (hc.1.trans hc.2)))
    (hZ : (Z, c) ∈ E.domain) : Function.Bijective (E.differential Z c hZ) := by
  let L := (E.differential Z c hZ).toLinearMap
  have hinj : Function.Injective L := (injective_iff_map_eq_zero L).mpr
    (fun W hW => exponential_prefix_kernel_eq_zero hCoordinates hM04 hM12 E Z W hb hc hmin hZ hW)
  let : FiniteDimensional ℝ (G.Horizontal (E.gamma Z c)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal (E.gamma Z c)
  have hdim : Module.finrank ℝ (G.Horizontal x) = Module.finrank ℝ (G.Horizontal (E.gamma Z c)) :=
    (VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x).trans
      (VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal (E.gamma Z c)).symm
  exact (LinearEquiv.ofInjectiveOfFinrankEq L hinj hdim).bijective

end PoincareMT.M14
