import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Function

universe u

namespace PoincareConjecture.CapModelEquivalence

variable {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ M']

noncomputable def transport_m28 {kind : CapModelKind} {p : RealProjectiveThree} {V : Set M}
    (C : CapModelEquivalence kind p V)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M' ∞) (hsource : e.source = V) :
    CapModelEquivalence kind p e.target where
  model := C.model
  model_topology := C.model_topology
  model_charted := C.model_charted
  model_manifold := C.model_manifold
  standard_model := C.standard_model
  standard_smooth := C.standard_smooth
  forward := C.forward ∘ e.symm
  inverse := e ∘ C.inverse
  inverse_mem y := e.map_source (hsource.symm ▸ C.inverse_mem y)
  left_inverse x hx := by
    change e (C.inverse (C.forward (e.symm x))) = x
    rw [C.left_inverse _ (hsource ▸ e.map_target hx)]
    exact e.right_inv hx
  right_inverse y := by
    change C.forward (e.symm (e (C.inverse y))) = y
    exact (congrArg C.forward (e.left_inv (hsource.symm ▸ C.inverse_mem y))).trans
      (C.right_inverse y)
  forward_smooth := by
    let := C.model_topology
    let := C.model_charted
    let := C.model_manifold
    exact C.forward_smooth.comp e.contMDiffOn_invFun
      (fun _ hx => hsource ▸ e.map_target hx)
  inverse_smooth := by
    let := C.model_topology
    let := C.model_charted
    let := C.model_manifold
    exact e.contMDiffOn_toFun.comp C.inverse_smooth
      (fun y _ => hsource.symm ▸ C.inverse_mem y)

end PoincareConjecture.CapModelEquivalence
