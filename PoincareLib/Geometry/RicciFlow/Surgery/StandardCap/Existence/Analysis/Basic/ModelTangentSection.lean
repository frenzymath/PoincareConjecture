import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth assembly of a model-space tangent vector

This is the model tangent-bundle homeomorphism with the product chart
instance made explicit. It supports the actual square-root path extensions
in Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M34

set_option backward.isDefEq.respectTransparency false in
/-- Pairing a model point and its tangent vector is smooth in the product
manifold structure, for every differentiability order. -/
theorem contMDiff_modelTangentMk
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (m : ℕ∞ω) :
    ContMDiff (I.prod 𝓘(𝕜, E)) I.tangent m
      (fun p : H × E => (⟨p.1, p.2⟩ : TangentBundle I H)) := by
  convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := I) (n := m)) using 1
  rw [chartedSpaceSelf_prod]
  rfl

end PoincareMT.M34
