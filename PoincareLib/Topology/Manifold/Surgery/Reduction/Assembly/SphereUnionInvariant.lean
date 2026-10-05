import PoincareLib.Topology.Manifold.ConnectedSum.SphereReduction

/-!
# Finite unions of smooth three-spheres

The initial disjoint union in a finite connected-sum assembly is a union of
spheres when all supplied factors are spheres. At the terminal carrier,
connectedness makes a nonempty clopen region equal to the whole carrier,
so its region identification is a global diffeomorphism. This is the base
and terminal bookkeeping in Morgan--Tian Corollary 15.4(2), pp. 358-359.
See `proof-work/tasks/M74/derivations/sphere-union.md` for the argument.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

namespace SmoothDisjointUnionData

variable {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {C : GeneralizedSliceCarrier.{u}}

/-- In a connected target, every nonempty displayed clopen region is the
whole carrier. Source: the terminal component selection in Morgan--Tian
Corollary 15.4(2), pp. 358-359; see `derivations/sphere-union.md`. -/
theorem region_eq_univ_of_isConnected (D : SmoothDisjointUnionData pieces C)
    (hC : IsConnected (Set.univ : Set C.carrier)) (i : Fin n)
    (hi : (D.region i).Nonempty) : D.region i = Set.univ := by
  let : PreconnectedSpace C.carrier := ⟨hC.isPreconnected⟩
  exact IsClopen.eq_univ ⟨D.region_closed i, D.region_open i⟩ hi

/-- A connected nonempty smooth disjoint union is diffeomorphic to one of
its displayed pieces. No separate piece-nonemptiness premise is needed. Source:
Morgan--Tian Corollary 15.4(2), pp. 358-359; see `derivations/sphere-union.md`. -/
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

/-- A carrier is a finite smooth disjoint union of factors diffeomorphic
to the standard three-sphere. The empty family is allowed. This is the
component invariant for Morgan--Tian Corollary 15.4(2), pp. 358-359;
see `derivations/sphere-union.md`. -/
def SphereUnion (C : GeneralizedSliceCarrier.{u}) : Prop :=
  ∃ (n : ℕ) (pieces : Fin n → GeneralizedSliceCarrier.{u}),
    Nonempty (SmoothDisjointUnionData pieces C) ∧
      ∀ i, Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)

namespace SphereUnion

/-- A displayed disjoint union of sphere factors satisfies the sphere-union
invariant. Source: the initial disjoint union in Morgan--Tian Corollary
15.4(2), pp. 358-359. -/
theorem of_disjointUnion {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (D : SmoothDisjointUnionData pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion C :=
  ⟨n, pieces, ⟨D⟩, hpieces⟩

/-- The initial carrier of an assembly of sphere factors satisfies the
sphere-union invariant. Source: the finite induction in Morgan--Tian
Corollary 15.4(2), pp. 358-359. -/
theorem initial {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (A : SmoothFiniteConnectedSumAssembly pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion A.initial :=
  of_disjointUnion A.disjoint_union hpieces

/-- A connected finite sphere union is diffeomorphic to the standard
three-sphere. Source: the terminal step of Morgan--Tian Corollary 15.4(2),
pp. 358-359; see `derivations/sphere-union.md`. -/
theorem nonempty_diffeomorph_threeSphere {C : GeneralizedSliceCarrier.{u}}
    (h : SphereUnion C) (hC : IsConnected (Set.univ : Set C.carrier)) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞) := by
  obtain ⟨n, pieces, ⟨D⟩, hpieces⟩ := h
  obtain ⟨i, ⟨e⟩⟩ := D.exists_diffeomorph_of_isConnected hC
  obtain ⟨d⟩ := hpieces i
  exact ⟨e.symm.trans d⟩

end SphereUnion
end M74
end PoincareMT
