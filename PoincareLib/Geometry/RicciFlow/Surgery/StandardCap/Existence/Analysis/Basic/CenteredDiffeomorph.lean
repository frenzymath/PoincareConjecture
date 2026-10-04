import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Translation and recentering of partial diffeomorphisms

Translation in a normed model space has identity differential and gives
recentered source coordinates of any differentiability order.
Application: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Addition by a fixed vector as a diffeomorphism, of any smoothness
order (used in Proposition 12.13, pp. 304-306). -/
noncomputable def modelTranslationDiffeomorph (x : E) (m : ℕ∞ω := ∞) :
    Diffeomorph (𝓘(𝕜, E)) (𝓘(𝕜, E)) E E m where
  toEquiv := (Homeomorph.addLeft x).toEquiv
  contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.add contDiff_id).contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- Translation has the identity manifold derivative, regardless of the
recorded smoothness order (Proposition 12.13, pp. 304-306). -/
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

/-- Recenter the normed source of any partial diffeomorphism by a
translation (Proposition 12.13, pp. 304-306). -/
noncomputable def centeredDiffeomorph (e : PartialDiffeomorph (𝓘(𝕜, E)) I E M m)
    (x : E) : PartialDiffeomorph (𝓘(𝕜, E)) I E M m :=
  (modelTranslationDiffeomorph (𝕜 := 𝕜) x m).toPartialDiffeomorph.trans e

/-- The recentered source is exactly the translated original source
(Proposition 12.13, pp. 304-306). -/
theorem centeredDiffeomorph_mem_source (e : PartialDiffeomorph (𝓘(𝕜, E)) I E M m)
    (x z : E) : z ∈ (centeredDiffeomorph e x).source ↔ x + z ∈ e.source := by
  change z ∈ (univ : Set E) ∩ (fun y => x + y) ⁻¹' e.source ↔ _
  simp

end PoincareMT.M34
