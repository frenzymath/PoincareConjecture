import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas











set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace ContDiffOn

section Derivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} {f : E → F} {g : F → E} {s : Set E}




theorem fderiv_injective_of_leftInvOn
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g (f '' s))
    (hs : IsOpen s) (hleft : LeftInvOn g f s) (hn : n ≠ 0)
    {x : E} (hx : x ∈ s) : Function.Injective (fderiv 𝕜 f x) := by
  have hfx := (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt hn
  have hgx := (hg (f x) (mem_image_of_mem f hx)).differentiableWithinAt hn
  have hmaps : ∀ᶠ y in 𝓝 x, f y ∈ f '' s := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact mem_image_of_mem f hy
  have hcomp := hgx.hasFDerivWithinAt.comp_hasFDerivAt x hfx.hasFDerivAt hmaps
  have hid : HasFDerivAt (g ∘ f) (ContinuousLinearMap.id 𝕜 E) x := by
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hleft hy
  have hlin := hcomp.unique hid
  have hlinleft : Function.LeftInverse (fderivWithin 𝕜 g (f '' s) (f x))
      (fderiv 𝕜 f x) := by
    intro v
    have hv := congrArg (fun L : E →L[𝕜] E => L v) hlin
    simpa using hv
  exact hlinleft.injective

end Derivative

section OpenChart

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {n : ℕ∞ω} {f : E → F} {g : F → E} {s : Set E}




theorem isOpen_image_of_leftInvOn
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g (f '' s))
    (hs : IsOpen s) (hleft : LeftInvOn g f s) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) : IsOpen (f '' s) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hinj := hf.fderiv_injective_of_leftInvOn hg hs hleft hn hx
  have hsurj : Function.Surjective (fderiv 𝕜 f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let A : E ≃L[𝕜] F := ContinuousLinearEquiv.ofBijective (fderiv 𝕜 f x)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  have hfx := hf.contDiffAt (hs.mem_nhds hx)
  have hderiv : HasFDerivAt f A.toContinuousLinearMap x :=
    (hfx.differentiableAt hn).hasFDerivAt
  rw [← (hfx.hasStrictFDerivAt' hderiv hn).map_nhds_eq_of_equiv]
  exact image_mem_map (hs.mem_nhds hx)





theorem exists_openPartialHomeomorph_of_leftInvOn
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g (f '' s))
    (hs : IsOpen s) (hleft : LeftInvOn g f s) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ∃ e : OpenPartialHomeomorph E F,
      e.source = s ∧ e.target = f '' s ∧ (e : E → F) = f ∧
      (e.symm : F → E) = g ∧ ContDiffOn 𝕜 n e e.source ∧
      ContDiffOn 𝕜 n e.symm e.target := by
  let e : OpenPartialHomeomorph E F := {
    toFun := f
    invFun := g
    source := s
    target := f '' s
    map_source' := fun _ hx => mem_image_of_mem f hx
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [hleft hx] using hx
    left_inv' := hleft
    right_inv' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hleft hx]
    open_source := hs
    open_target := hf.isOpen_image_of_leftInvOn hg hs hleft hn hdim
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn }
  exact ⟨e, rfl, rfl, rfl, rfl, hf, hg⟩

end OpenChart

end ContDiffOn
