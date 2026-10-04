import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.PlaneProjectionSmoothness
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EuclideanPlaneTopology

/-!
# Smooth affine-leaf fields in geometric plane coordinates

Smoothness is measured by the actual orthogonal projectors; local
constancy is along the assigned affine planes. Thus local normalized
operators supply the invariant without a global frame. See Cairns
1940, pp. 800--801, 804--805 and M76 derivation 60.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A smooth geometric plane field that is locally constant along
each assigned affine plane. Rank and transversality are separate
requirements. See Cairns Hypotheses III--IV, p. 804 and M76 derivation 60. -/
structure IsSmoothLeafFieldOn (P : E → EuclideanSubspace E) (U : Set E) : Prop where
  /-- Smoothness in the actual projector coordinates; Cairns pp. 800, 804. -/
  contDiffOn_projector : ContDiffOn ℝ ∞ (fun x => (P x).subspace.starProjection) U
  /-- The geometric field is constant locally along each leaf; Cairns p. 804. -/
  eventually_eq : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (P x).subspace → P y = P x

/-- A constant plane gives a smooth affine-leaf field on every
domain. See Cairns initial step, p. 804 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.const (P : EuclideanSubspace E) (U : Set E) :
    IsSmoothLeafFieldOn (fun _ => P) U :=
  ⟨contDiffOn_const, fun _ _ => Eventually.of_forall (fun _ _ => rfl)⟩

/-- Restricting the ambient domain preserves the smooth leaf
invariant. See Cairns pp. 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.mono {P : E → EuclideanSubspace E} {U V : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hVU : V ⊆ U) : IsSmoothLeafFieldOn P V :=
  ⟨hP.contDiffOn_projector.mono hVU, fun x hx => hP.eventually_eq x (hVU hx)⟩

/-- A smooth geometric leaf field is continuous in the actual
plane topology. See Cairns pp. 800, 804 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.continuousOn {P : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) : ContinuousOn P U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_iff_projector.mpr hP.contDiffOn_projector.continuousOn.domRestrict

/-- Equal fields on an open domain have the same smooth leaf
invariant, irrespective of their total values outside it.
See Cairns pp. 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.congr {P Q : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hU : IsOpen U) (hQP : EqOn Q P U) :
    IsSmoothLeafFieldOn Q U := by
  refine ⟨hP.contDiffOn_projector.congr (fun x hx =>
    congrArg (fun R : EuclideanSubspace E => R.subspace.starProjection) (hQP hx)), ?_⟩
  intro x hx
  filter_upwards [hU.mem_nhds hx, hP.eventually_eq x hx] with y hy hconst hxy
  rw [hQP hy, hQP hx]
  apply hconst
  simpa only [hQP hx] using hxy

/-- Smooth leaf regularity is local on a union of open ambient
domains. See Cairns pp. 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.union {P : E → EuclideanSubspace E} {U V : Set E}
    (hPU : IsSmoothLeafFieldOn P U) (hPV : IsSmoothLeafFieldOn P V)
    (hU : IsOpen U) (hV : IsOpen V) : IsSmoothLeafFieldOn P (U ∪ V) := by
  refine ⟨hPU.contDiffOn_projector.union_of_isOpen hPV.contDiffOn_projector hU hV, ?_⟩
  rintro x (hx | hx)
  · exact hPU.eventually_eq x hx
  · exact hPV.eventually_eq x hx

/-- A smooth surjective operator field locally constant on its
kernel leaves supplies a smooth geometric plane field. Its
coordinate frame need only be local. See Cairns pp. 800--801,
804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.of_operator {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Q : E → E →L[ℝ] F} {U : Set E} (hQ : ContDiffOn ℝ ∞ Q U)
    (hsurj : ∀ x ∈ U, Function.Surjective (Q x))
    (hleaf : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x) :
    IsSmoothLeafFieldOn (fun x => ⟨(Q x).ker⟩) U := by
  refine ⟨hQ.ker_starProjection hsurj, ?_⟩
  intro x hx
  filter_upwards [hleaf x hx] with y hy hxy
  exact congrArg (fun R : E →L[ℝ] F => (⟨R.ker⟩ : EuclideanSubspace E)) (hy hxy)

end Geometry.EuclideanSubspace
