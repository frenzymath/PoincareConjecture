import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapModelEquivalence

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  {kind : CapModelKind} {p : RealProjectiveThree}

noncomputable def transport
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (K : CapModelEquivalence kind p e.source) :
    CapModelEquivalence kind p e.target where
  model := K.model
  model_topology := K.model_topology
  model_charted := K.model_charted
  model_manifold := K.model_manifold
  standard_model := K.standard_model
  standard_smooth := K.standard_smooth
  forward := K.forward ∘ e.symm
  inverse := e ∘ K.inverse
  inverse_mem := fun y => e.toPartialEquiv.map_source (K.inverse_mem y)
  left_inverse := by
    intro x hx
    exact (congrArg (fun y => e y)
      (K.left_inverse _ (e.toPartialEquiv.map_target hx))).trans
      (e.toPartialEquiv.right_inv hx)
  right_inverse := by
    intro y
    exact (congrArg K.forward (e.toPartialEquiv.left_inv (K.inverse_mem y))).trans
      (K.right_inverse y)
  forward_smooth := by
    let : TopologicalSpace K.model := K.model_topology
    let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.model := K.model_charted
    let : IsManifold (𝓡 3) ∞ K.model := K.model_manifold
    exact K.forward_smooth.comp e.contMDiffOn_invFun
      (fun _ hx => e.toPartialEquiv.map_target hx)
  inverse_smooth := by
    let : TopologicalSpace K.model := K.model_topology
    let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.model := K.model_charted
    let : IsManifold (𝓡 3) ∞ K.model := K.model_manifold
    exact e.contMDiffOn_toFun.comp K.inverse_smooth (fun y _ => K.inverse_mem y)

end PoincareConjecture.CapModelEquivalence
