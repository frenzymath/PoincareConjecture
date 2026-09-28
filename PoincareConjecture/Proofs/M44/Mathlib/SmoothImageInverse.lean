import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] in

theorem mfderiv_bijective_of_smooth_leftInvOn
    {f : M → N} {inverse : N → M} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ inverse (f '' U))
    (hleft : LeftInvOn inverse f U) {x : M} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := by
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hunique := hU.uniqueMDiffWithinAt (I := 𝓡 n) hx
  have hcomp := mfderivWithin_comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n) x
    ((hi _ (mem_image_of_mem f hx)).mdifferentiableWithinAt (by simp))
    ((hf x hx).mdifferentiableWithinAt (by simp)) (mapsTo_image f U) hunique
  have hid : mfderivWithin (𝓡 n) (𝓡 n) (inverse ∘ f) U x =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x) := by
    exact (mfderivWithin_congr_of_mem (I := 𝓡 n) (I' := 𝓡 n)
      (f₁ := inverse ∘ f) (f := id) (fun _ hy => hleft hy) hx).trans
      (mfderivWithin_id hunique)
  rw [hid, mfderivWithin_eq_mfderiv hunique
    (hfx.mdifferentiableAt (by simp))] at hcomp
  have hleftD : Function.LeftInverse
      (mfderivWithin (𝓡 n) (𝓡 n) inverse (f '' U) (f x))
      (mfderiv (𝓡 n) (𝓡 n) f x) := by
    intro v
    exact (congrArg (fun L => L v) hcomp).symm
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) (f x)) := rfl
  exact ⟨hleftD.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hleftD.injective⟩

theorem isOpen_image_of_smooth_leftInvOn
    {f : M → N} {inverse : N → M} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ inverse (f '' U))
    (hleft : LeftInvOn inverse f U) : IsOpen (f '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    ((hf x hx).contMDiffAt (hU.mem_nhds hx))
    (mfderiv_bijective_of_smooth_leftInvOn hU hf hi hleft hx)]
  exact image_mem_map (hU.mem_nhds hx)

theorem contMDiffAt_inverse_of_smooth_leftInvOn
    {f : M → N} {inverse : N → M} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ inverse (f '' U))
    (hleft : LeftInvOn inverse f U) {y : N} (hy : y ∈ f '' U) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ inverse y :=
  (hi y hy).contMDiffAt ((isOpen_image_of_smooth_leftInvOn hU hf hi hleft).mem_nhds hy)

end Poincare
