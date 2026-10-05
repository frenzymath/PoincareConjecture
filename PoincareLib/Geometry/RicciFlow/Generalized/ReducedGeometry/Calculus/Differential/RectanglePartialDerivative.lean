import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.RectanglePartialTangent

/-!
# Coordinate partial derivatives on a closed-by-open rectangle

Morgan-Tian Proposition 6.33, pp. 120-121. Projecting the actual
rectangle partial tangents onto the model vector gives smooth coordinate
partials, including closed time endpoints.
-/

set_option autoImplicit false
-- The product self-model is identified with the self-model of the product.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {S P : Set 𝕜} {q : 𝕜 × 𝕜 → E} {m k : ℕ∞ω}

/-- The actual within time partial is smooth on a rectangle with
unique derivatives in both factors, Proposition 6.33, pp. 120-121. -/
theorem ContDiffOn.contDiffOn_derivWithin_fst_prod (hq : ContDiffOn 𝕜 m q (S ×ˢ P))
    (hS : UniqueDiffOn 𝕜 S) (hP : UniqueDiffOn 𝕜 P) (hkm : k + 1 ≤ m) :
    ContDiffOn 𝕜 k (fun z => derivWithin (fun r => q (r, z.2)) S z.1) (S ×ˢ P) := by
  have hM : ContMDiffOn ((𝓘(𝕜, 𝕜)).prod (𝓘(𝕜, 𝕜))) (𝓘(𝕜, E)) m q (S ×ˢ P) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hq.contMDiffOn
  have htan := hM.contMDiffOn_partialTangentWithin_fst_prod hS hP (1 : 𝕜) hkm
  have h := (contMDiff_snd_tangentBundle_modelSpace E (𝓘(𝕜, E)) (n := k)).comp_contMDiffOn htan
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  convert h.contDiffOn using 1
  funext z
  simp only [Function.comp_def, mfderivWithin_eq_fderivWithin, derivWithin]
  rfl

/-- The unrestricted parameter partial remains smooth on the closed
rectangle when its parameter factor is open, Proposition 6.33,
pp. 120-121. Iteration gives the actual second parameter partial. -/
theorem ContDiffOn.contDiffOn_deriv_snd_prod (hq : ContDiffOn 𝕜 m q (S ×ˢ P))
    (hS : UniqueDiffOn 𝕜 S) (hP : IsOpen P) (hkm : k + 1 ≤ m) :
    ContDiffOn 𝕜 k (fun z => deriv (fun r => q (z.1, r)) z.2) (S ×ˢ P) := by
  have hM : ContMDiffOn ((𝓘(𝕜, 𝕜)).prod (𝓘(𝕜, 𝕜))) (𝓘(𝕜, E)) m q (S ×ˢ P) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hq.contMDiffOn
  have htan := hM.contMDiffOn_partialTangent_snd_prod hS hP (1 : 𝕜) hkm
  have h := (contMDiff_snd_tangentBundle_modelSpace E (𝓘(𝕜, E)) (n := k)).comp_contMDiffOn htan
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  convert h.contDiffOn using 1
  funext z
  simp only [Function.comp_def, mfderiv_eq_fderiv, deriv]
  rfl
