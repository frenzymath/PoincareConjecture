import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]



noncomputable def modelTranslationDiffeomorph (x : E) (m : ℕ∞ω := ∞) :
    Diffeomorph (𝓘(𝕜, E)) (𝓘(𝕜, E)) E E m where
  toEquiv := (Homeomorph.addLeft x).toEquiv
  contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.add contDiff_id).contMDiff

set_option backward.isDefEq.respectTransparency false in


theorem modelTranslationDiffeomorph_mfderiv (x z : E) (m : ℕ∞ω := ∞) :
    mfderiv (𝓘(𝕜, E)) (𝓘(𝕜, E)) (modelTranslationDiffeomorph (𝕜 := 𝕜) x m) z =
      ContinuousLinearMap.id 𝕜 E := by
  have hd : HasFDerivAt (fun y : E => x + y) (ContinuousLinearMap.id 𝕜 E) z :=
    (hasFDerivAt_id z).const_add x
  apply ContinuousLinearMap.ext
  intro v
  change mfderiv (𝓘(𝕜, E)) (𝓘(𝕜, E)) (fun y => x + y) z v = v
  rw [mfderiv_eq_fderiv]
  convert! congrArg (fun L : E →L[𝕜] E => L v) hd.fderiv using 1

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E' H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ∞ω}



noncomputable def centeredDiffeomorph (e : PartialDiffeomorph (𝓘(𝕜, E)) I E M m)
    (x : E) : PartialDiffeomorph (𝓘(𝕜, E)) I E M m :=
  (modelTranslationDiffeomorph (𝕜 := 𝕜) x m).toPartialDiffeomorph.trans e



theorem centeredDiffeomorph_mem_source (e : PartialDiffeomorph (𝓘(𝕜, E)) I E M m)
    (x z : E) : z ∈ (centeredDiffeomorph e x).source ↔ x + z ∈ e.source := by
  change z ∈ (univ : Set E) ∩ (fun y => x + y) ⁻¹' e.source ↔ _
  simp

end PoincareConjecture.M34
