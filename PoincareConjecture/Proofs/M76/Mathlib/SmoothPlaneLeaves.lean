import PoincareConjecture.Proofs.M76.Mathlib.PlaneProjectionSmoothness
import PoincareConjecture.Proofs.M76.Mathlib.EuclideanPlaneTopology

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

structure IsSmoothLeafFieldOn (P : E → EuclideanSubspace E) (U : Set E) : Prop where

  contDiffOn_projector : ContDiffOn ℝ ∞ (fun x => (P x).subspace.starProjection) U

  eventually_eq : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (P x).subspace → P y = P x

theorem IsSmoothLeafFieldOn.const (P : EuclideanSubspace E) (U : Set E) :
    IsSmoothLeafFieldOn (fun _ => P) U :=
  ⟨contDiffOn_const, fun _ _ => Eventually.of_forall (fun _ _ => rfl)⟩

theorem IsSmoothLeafFieldOn.mono {P : E → EuclideanSubspace E} {U V : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hVU : V ⊆ U) : IsSmoothLeafFieldOn P V :=
  ⟨hP.contDiffOn_projector.mono hVU, fun x hx => hP.eventually_eq x (hVU hx)⟩

theorem IsSmoothLeafFieldOn.continuousOn {P : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) : ContinuousOn P U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_iff_projector.mpr hP.contDiffOn_projector.continuousOn.domRestrict

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

theorem IsSmoothLeafFieldOn.union {P : E → EuclideanSubspace E} {U V : Set E}
    (hPU : IsSmoothLeafFieldOn P U) (hPV : IsSmoothLeafFieldOn P V)
    (hU : IsOpen U) (hV : IsOpen V) : IsSmoothLeafFieldOn P (U ∪ V) := by
  refine ⟨hPU.contDiffOn_projector.union_of_isOpen hPV.contDiffOn_projector hU hV, ?_⟩
  rintro x (hx | hx)
  · exact hPU.eventually_eq x hx
  · exact hPV.eventually_eq x hx

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
