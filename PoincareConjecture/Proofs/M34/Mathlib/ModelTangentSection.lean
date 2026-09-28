import Mathlib.Geometry.Manifold.VectorBundle.Tangent









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in


theorem contMDiff_modelTangentMk
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (m : ℕ∞ω) :
    ContMDiff (I.prod 𝓘(𝕜, E)) I.tangent m
      (fun p : H × E => (⟨p.1, p.2⟩ : TangentBundle I H)) := by
  convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := I) (n := m)) using 1
  rw [chartedSpaceSelf_prod]
  rfl

end PoincareConjecture.M34
