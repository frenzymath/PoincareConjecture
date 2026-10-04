import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder

/-!
# Local equality of actual cylinder metric comparisons

Equality on the open axial strip preserves the frozen spatial jet
recursion and its strict uniform bound. This is the top-slice adapter
from Definition 9.78 to the necks in section 10.3.1, p. 247, of
Morgan--Tian. See task derivation 15.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M28

/-- Tensor equality on an open axial strip identifies actual fixed-chart
coefficients (Definition 2.16, p. 30; task derivation 15). -/
theorem cylinderCoefficient_eq_of_strip
    {B C : RoundCylinderTwoTensor} {a b : ℝ}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo a b → ∀ v w, B z v w = C z v w)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {p : RoundCylinderCoordinates} (hp : p.2 ∈ Ioo a b) (i j : Fin 3) :
    roundCylinderTensorCoefficient B c p i j = roundCylinderTensorCoefficient C c p i j :=
  h (c.symm p.1, p.2) hp _ _

/-- All actual covariant error jets depend only on the tensor on the open
strip, with every earlier derivative slot retained (task derivation 15). -/
theorem cylinderIteratedDerivative_eq_of_strip
    {B C : RoundCylinderTwoTensor} {a b : ℝ}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo a b → ∀ v w, B z v w = C z v w)
    (u : ℝ) (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) {p : RoundCylinderCoordinates} (hp : p.2 ∈ Ioo a b) :
    roundCylinderIteratedDerivative u c B k p =
      roundCylinderIteratedDerivative u c C k p := by
  induction k generalizing p with
  | zero =>
      funext v
      simp only [roundCylinderIteratedDerivative, cylinderCoefficient_eq_of_strip h c hp]
  | succ k ih =>
      funext v
      have heq : (fun q => roundCylinderIteratedDerivative u c B k q
          (fun i => v i.succ)) =ᶠ[𝓝 p]
          (fun q => roundCylinderIteratedDerivative u c C k q (fun i => v i.succ)) := by
        filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
          (isOpen_Ioo.mem_nhds hp)] with q hq
        exact congrFun (ih hq) _
      have hd := heq.fderiv_eq (𝕜 := ℝ)
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative, ih hp]
      apply congrArg (fun r : ℝ => r - _)
      exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
        L (roundCylinderCoordinateBasis (v 0))) hd

/-- The frozen squared jet errors agree under open-strip tensor equality
(Definition 2.16, p. 30; task derivation 15). -/
theorem cylinderJetErrorSquared_eq_of_strip
    {B C : RoundCylinderTwoTensor} {a b : ℝ}
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo a b → ∀ v w, B z v w = C z v w)
    (u : ℝ) (k : ℕ) {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo a b) :
    roundCylinderJetErrorSquared u B k z = roundCylinderJetErrorSquared u C k z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinderIteratedDerivative_eq_of_strip h u _ j hz]

/-- Open-strip equality transfers the actual coordinate smoothness in
the metric comparison (task derivation 15). -/
theorem cylinderTensorSmoothOn_of_eqOn_strip {epsilon : ℝ}
    {B C : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B)
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = C z v w) : RoundCylinderTensorSmoothOn epsilon C := by
  intro q i j
  exact (hB q i j).congr (fun p hp =>
    (cylinderCoefficient_eq_of_strip h _ hp.2 i j).symm)

/-- A frozen strict comparison transfers with its original uniform
witness under equality on the actual cylinder (task derivation 15). -/
theorem cylinderClose_of_eqOn_strip {epsilon u : ℝ} {B C : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon u B)
    (h : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = C z v w) : RoundCylinderClose epsilon u C := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨cylinderTensorSmoothOn_of_eqOn_strip hsmooth h, bound, hbound, ?_⟩
  intro z hz
  rw [← cylinderJetErrorSquared_eq_of_strip h u _ hz]
  exact hjet z hz

end PoincareMT.M28
