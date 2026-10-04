import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
# Transport of the actual smooth cap model

Morgan--Tian Definition 9.72, pp. 230-231, and Proposition 9.79,
pp. 232-234. An actual partial diffeomorphism transports every field of
the frozen smooth model witness. This same-universe construction keeps
the model type and its standard smooth witness unchanged.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Function

universe u

namespace PoincareMT.CapModelEquivalence

variable {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ M']

/-- Transport the complete frozen smooth-model equivalence through an
actual partial diffeomorphism on its carrier, as required by the cap
recut in Proposition 9.79, pp. 232-234. Both ambient manifolds and the
retained model live in the same universe. -/
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

end PoincareMT.CapModelEquivalence
