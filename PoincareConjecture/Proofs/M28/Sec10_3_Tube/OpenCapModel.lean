import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CapModelEquivalence

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

noncomputable def restrictOpen {kind : CapModelKind} {p : RealProjectiveThree}
    {S : Set M} (A : CapModelEquivalence kind p S)
    (V : TopologicalSpace.Opens M) (hSV : S ⊆ (V : Set M)) :
    CapModelEquivalence kind p ((Subtype.val : V → M) ⁻¹' S) where
  model := A.model
  model_topology := A.model_topology
  model_charted := A.model_charted
  model_manifold := A.model_manifold
  standard_model := A.standard_model
  standard_smooth := A.standard_smooth
  forward := A.forward ∘ Subtype.val
  inverse y := ⟨A.inverse y, hSV (A.inverse_mem y)⟩
  inverse_mem y := A.inverse_mem y
  left_inverse x hx := Subtype.ext (A.left_inverse x hx)
  right_inverse y := A.right_inverse y
  forward_smooth := by
    let := A.model_topology
    let := A.model_charted
    let := A.model_manifold
    exact A.forward_smooth.comp
      (contMDiff_subtype_val (I := 𝓡 3) (U := V)).contMDiffOn
      (fun _ hx => hx)
  inverse_smooth := by
    let := A.model_topology
    let := A.model_charted
    let := A.model_manifold
    intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff V _ univ y).mp
    exact A.inverse_smooth y hy

end PoincareConjecture.CapModelEquivalence
