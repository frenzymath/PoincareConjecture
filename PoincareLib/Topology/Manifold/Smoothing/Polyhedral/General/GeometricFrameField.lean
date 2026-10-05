import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.SmoothPlaneLeaves
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FramePlaneCoordinates

/-!
# A common-frame representative of a geometric smooth leaf field

Where the planes complement a fixed frame, their Gram formula
gives one smooth normalized operator field with exactly the same
geometric kernels and local leaf constancy. See Cairns 1940,
pp. 800--801, 804--805 and M76 derivation 60.
-/

set_option autoImplicit false

open Set Filter Geometry
open scoped Topology ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The geometric frame formula fixes the frame and has exactly
the prescribed complementary plane as its kernel.
See Cairns p. 801 and M76 derivation 60. -/
theorem frameProjectionFormula_spec (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (P : EuclideanSubspace E) (hP : IsCompl J.range P.subspace) :
    Function.RightInverse J (frameProjectionFormula J P.subspace.starProjection) ∧
      (frameProjectionFormula J P.subspace.starProjection).ker = P.subspace := by
  let Q := J.frameComplementPlaneHomeomorph hJ ⟨P, hP⟩
  have hker : Q.val.ker = P.subspace := J.ker_frameComplementPlaneHomeomorph hJ ⟨P, hP⟩
  have he : frameProjectionFormula J P.subspace.starProjection = Q.val := by
    simpa only [hker] using Q.val.frameProjectionFormula_ker J Q.property
  rw [he]
  exact ⟨Q.property, hker⟩

end ContinuousLinearMap

namespace Geometry.EuclideanSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Complementarity to one frame on a domain provides a single
smooth normalized representative of a geometric leaf field there,
with exact kernels and local leaf constancy.
See Cairns pp. 801, 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.exists_frameRepresentation {P : E → EuclideanSubspace E}
    {U : Set E} (hP : IsSmoothLeafFieldOn P U) (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (hcompl : ∀ x ∈ U, IsCompl J.range (P x).subspace) :
    ∃ Q : E → E →L[ℝ] F, ContDiffOn ℝ ∞ Q U ∧
      (∀ x ∈ U, Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace) ∧
      ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x := by
  let Q : E → E →L[ℝ] F := fun x =>
    ContinuousLinearMap.frameProjectionFormula J (P x).subspace.starProjection
  have hspec (x : E) (hx : x ∈ U) :
      Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace :=
    J.frameProjectionFormula_spec hJ (P x) (hcompl x hx)
  refine ⟨Q, ?_, hspec, ?_⟩
  · intro x hx
    have hi := (Q x).injective_perpendicularFrame_of_rightInverse J (hspec x hx).1
    have hi' : Function.Injective (ContinuousLinearMap.perpendicularFrame J
        (P x).subspace.starProjection) := by
      simpa only [(hspec x hx).2] using hi
    exact (J.contDiffAt_frameProjectionFormula _ hi').comp_contDiffWithinAt x
      (hP.contDiffOn_projector x hx)
  · intro x hx
    filter_upwards [hP.eventually_eq x hx] with y hy hxy
    rw [(hspec x hx).2] at hxy
    exact congrArg (fun R : EuclideanSubspace E =>
      ContinuousLinearMap.frameProjectionFormula J R.subspace.starProjection) (hy hxy)

end Geometry.EuclideanSubspace
