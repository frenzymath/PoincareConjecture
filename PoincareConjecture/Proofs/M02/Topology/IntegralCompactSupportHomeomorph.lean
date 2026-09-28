import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap
import PoincareConjecture.Proofs.M02.Topology.IntegralRelativeChains

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralCompactSupportCohomologyOpenMap_homeomorph_isIso
    [T2Space Y] (e : X ≃ₜ Y) (q : Nat) :
    IsIso (integralCompactSupportCohomologyOpenMap
      (e : C(X, Y)) e.isOpenEmbedding q) := by
  let : T2Space X := e.isEmbedding.t2Space
  let f : C(X, Y) := e
  let g : C(Y, X) := e.symm
  let hf : _root_.Topology.IsOpenEmbedding f := e.isOpenEmbedding
  let hg : _root_.Topology.IsOpenEmbedding g := e.symm.isOpenEmbedding
  let F := integralCompactSupportCohomologyOpenMap f hf q
  let G := integralCompactSupportCohomologyOpenMap g hg q
  have hFG : F ≫ G = 𝟙 _ := by
    change integralCompactSupportCohomologyOpenMap f hf q ≫
        integralCompactSupportCohomologyOpenMap g hg q = 𝟙 _
    rw [integralCompactSupportCohomologyOpenMap_comp]
    simp [f, g]
  have hGF : G ≫ F = 𝟙 _ := by
    change integralCompactSupportCohomologyOpenMap g hg q ≫
        integralCompactSupportCohomologyOpenMap f hf q = 𝟙 _
    rw [integralCompactSupportCohomologyOpenMap_comp]
    simp [f, g]
  exact ⟨G, hFG, hGF⟩

theorem integralHomeomorphHomologyMap_isIso
    (e : X ≃ₜ Y) (n : Nat) :
    IsIso (homologyMap
      (integralChainsFunctor.map (TopCat.ofHom (e : C(X, Y)))) n) := by
  change IsIso (integralHomeomorphHomologyIso e n).hom
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
