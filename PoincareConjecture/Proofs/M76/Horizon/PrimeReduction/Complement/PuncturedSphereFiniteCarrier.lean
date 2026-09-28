import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregionModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false
open Set Geometry

namespace Geometry.CubicalThreeSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem exists_finite_punctured_sphere_carrier {ι : Type*} [Finite ι]
    (a r : ι → Set V4) (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haS : ∀ i, a i ⊆ sphere)
    (hadis : Pairwise fun i j => Disjoint (a i) (a j))
    (hao : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a i \ r i))) :
    ∃ K : SimplicialComplex ℝ V4,
      K.faces.Finite ∧ K.space = sphere \ ⋃ i, a i \ r i := by
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := lower_ball
  obtain ⟨_,_,_,_,_,_,⟨_,⟨U,hU,hUs,_⟩,_⟩,_⟩ := upper_ball
  obtain ⟨K,hK,hKs⟩ := L.exists_finite_triangulation_union U hL hU
  rw [hLs,hUs,lower_union_upper] at hKs
  have hrelative := (punctured_sphere_relative_geometry a r ha haS hadis hao).1
  have hclosed : IsClosed (sphere \ ⋃ i, a i \ r i) := by
    have heq : (Subtype.val : sphere → V4) ''
        ((Subtype.val : sphere → V4) ⁻¹' (sphere \ ⋃ i, a i \ r i)) =
          sphere \ ⋃ i, a i \ r i :=
      image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using
        (sdiff_subset : sphere \ ⋃ i, a i \ r i ⊆ sphere))
    rw [← heq]
    exact isClosed_frontier.isClosedMap_subtype_val _ hrelative
  obtain ⟨_,P,_,_,_,_,_,hP,hPs,_⟩ :=
    K.exists_finite_closed_punctured_ball_carrier hK a r ha
      (fun i => (haS i).trans hKs.symm.subset) hadis (hKs.symm ▸ hclosed)
  exact ⟨P,hP,hPs.trans (by rw [hKs])⟩

end Geometry.CubicalThreeSphere
