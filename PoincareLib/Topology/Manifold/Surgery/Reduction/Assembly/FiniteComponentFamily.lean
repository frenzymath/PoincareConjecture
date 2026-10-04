import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.SphereUnionInvariant

/-!
# Enumerating reconstructed sphere components

A finite clopen family of regions in the target, with genuine smooth
identifications from sphere factors, gives the `Fin`-indexed sphere-union
invariant. This is the indexing step of Morgan--Tian Corollary 15.4,
pp. 358-359. The geometric region, identification, disjointness, and cover
obligations remain explicit inputs.
See `proof-work/tasks/M74/derivations/finite-component-family.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.M74

/-- Enumerate a finite clopen family of sphere regions as a sphere union.
The index type may be the option type of the untouched original indices,
with `none` representing the new core. Source: Morgan--Tian Corollary
15.4, pp. 358-359; see `derivations/finite-component-family.md`. -/
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

end PoincareMT.M74
