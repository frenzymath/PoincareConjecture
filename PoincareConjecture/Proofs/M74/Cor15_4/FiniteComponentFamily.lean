import PoincareConjecture.Proofs.M74.Cor15_4.SphereUnionInvariant

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M74

theorem SphereUnion.of_finite_regions {ι : Type v} [Finite ι]
    (pieces : ι → GeneralizedSliceCarrier.{u}) {C : GeneralizedSliceCarrier.{u}}
    (region : ι → Set C.carrier)
    (hopen : ∀ i, IsOpen (region i)) (hclosed : ∀ i, IsClosed (region i))
    (identify : ∀ i, SurgeryRegionEquivalence (pieces i) C Set.univ (region i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (region i) (region j))
    (hcover : (⋃ i, region i) = Set.univ)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion C := by
  let : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  let D : SmoothDisjointUnionData
      (fun j : Fin (Fintype.card ι) => pieces (e j)) C := {
    region := fun j => region (e j)
    region_open := fun j => hopen (e j)
    region_closed := fun j => hclosed (e j)
    identify := fun j => identify (e j)
    pairwise_disjoint := fun i j hij =>
      hdisjoint (e i) (e j) (fun h => hij (e.injective h))
    cover := (e.surjective.iUnion_comp region).trans hcover }
  exact SphereUnion.of_disjointUnion D (fun j => hpieces (e j))

end PoincareConjecture.M74
