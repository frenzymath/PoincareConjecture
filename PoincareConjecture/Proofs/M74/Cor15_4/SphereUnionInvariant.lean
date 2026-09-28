import PoincareConjecture.Definitions.M74ConnectedSumReduction

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

namespace SmoothDisjointUnionData

variable {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {C : GeneralizedSliceCarrier.{u}}

theorem region_eq_univ_of_isConnected (D : SmoothDisjointUnionData pieces C)
    (hC : IsConnected (Set.univ : Set C.carrier)) (i : Fin n)
    (hi : (D.region i).Nonempty) : D.region i = Set.univ := by
  let : PreconnectedSpace C.carrier := ⟨hC.isPreconnected⟩
  exact IsClopen.eq_univ ⟨D.region_closed i, D.region_open i⟩ hi

theorem exists_diffeomorph_of_isConnected (D : SmoothDisjointUnionData pieces C)
    (hC : IsConnected (Set.univ : Set C.carrier)) :
    ∃ i, Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier C.carrier ∞) := by
  obtain ⟨x, _⟩ := hC.nonempty
  have hx : x ∈ ⋃ i, D.region i := D.cover.symm ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hregion := D.region_eq_univ_of_isConnected hC i ⟨x, hi⟩
  refine ⟨i, ⟨{
    toFun := (D.identify i).map
    invFun := (D.identify i).inverse
    left_inv := fun y => (D.identify i).left_inverse (Set.mem_univ y)
    right_inv := ?_
    contMDiff_toFun := contMDiffOn_univ.mp (D.identify i).map_smooth
    contMDiff_invFun := ?_ }⟩⟩
  · intro y
    apply (D.identify i).right_inverse
    rw [hregion]
    exact Set.mem_univ y
  · change ContMDiff (𝓡 3) (𝓡 3) ∞ (D.identify i).inverse
    apply contMDiffOn_univ.mp
    simpa only [hregion] using (D.identify i).inverse_smooth

end SmoothDisjointUnionData

namespace M74

def SphereUnion (C : GeneralizedSliceCarrier.{u}) : Prop :=
  ∃ (n : ℕ) (pieces : Fin n → GeneralizedSliceCarrier.{u}),
    Nonempty (SmoothDisjointUnionData pieces C) ∧
      ∀ i, Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)

namespace SphereUnion

theorem of_disjointUnion {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (D : SmoothDisjointUnionData pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion C :=
  ⟨n, pieces, ⟨D⟩, hpieces⟩

theorem initial {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (A : SmoothFiniteConnectedSumAssembly pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion A.initial :=
  of_disjointUnion A.disjoint_union hpieces

theorem nonempty_diffeomorph_threeSphere {C : GeneralizedSliceCarrier.{u}}
    (h : SphereUnion C) (hC : IsConnected (Set.univ : Set C.carrier)) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞) := by
  obtain ⟨n, pieces, ⟨D⟩, hpieces⟩ := h
  obtain ⟨i, ⟨e⟩⟩ := D.exists_diffeomorph_of_isConnected hC
  obtain ⟨d⟩ := hpieces i
  exact ⟨e.symm.trans d⟩

end SphereUnion
end M74
end PoincareConjecture
