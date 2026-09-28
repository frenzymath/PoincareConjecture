import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.BallEulerCount
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceSpan
import Mathlib.Data.Finset.Powerset









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_tetrahedron_boundary_count_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∧
      (∀ s ∈ J.faces, s.card ≤ 3) ∧ J.surfaceEulerCount = 2 := by
  classical
  have hfacet (p : t) : t.erase p ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem p.2,ht4]; norm_num))
  let facet (p : t) : K.faces := ⟨t.erase p,hfacet p⟩
  let F : Finset K.faces := Finset.univ.image facet
  let J := K.finiteFaceSpan F
  have hfaces (a : Finset E) : a ∈ J.faces ↔ a.Nonempty ∧ a ⊂ t := by
    rw [K.finiteFaceSpan_faces]
    constructor
    · rintro ⟨ha,u,hu,hau⟩
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hu
      exact ⟨ha,Finset.ssubset_iff_exists_subset_erase.mpr ⟨p,p.2,hau⟩⟩
    · rintro ⟨ha,hat⟩
      obtain ⟨p,hpt,hap⟩ := Finset.ssubset_iff_exists_subset_erase.mp hat
      exact ⟨ha,facet ⟨p,hpt⟩,Finset.mem_image.mpr ⟨⟨p,hpt⟩,Finset.mem_univ _,rfl⟩,hap⟩
  have hspace : J.space = intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (K.indep ht).convexHull_subset_intrinsicFrontier ((hfaces a).mp ha).2 hxa
    · intro hx
      obtain ⟨p,hp,hxp⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ht) x).mp hx
      exact J.convexHull_subset_space ((hfaces _).mpr
        ⟨K.nonempty_of_mem_faces (hfacet ⟨p,hp⟩),Finset.erase_ssubset hp⟩) hxp
  have hcard (n : ℕ) (hn0 : 0 < n) (hn4 : n < 4) :
      Nat.card (J.FaceOfCard n) = Nat.choose 4 n := by
    have hmem (a : Finset E) : a ∈ t.powersetCard n ↔ a ∈ J.faces ∧ a.card = n := by
      rw [Finset.mem_powersetCard,hfaces]
      constructor
      · rintro ⟨hat,ha⟩
        refine ⟨⟨Finset.card_pos.mp (ha.symm ▸ hn0),?_⟩,ha⟩
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hat,fun he => by
          have hc := congrArg Finset.card he
          omega⟩
      · rintro ⟨⟨_,hat⟩,ha⟩
        exact ⟨Finset.Subset.trans (le_of_lt hat) (Finset.Subset.refl _),ha⟩
    calc
      Nat.card (J.FaceOfCard n) = (t.powersetCard n).card := Nat.subtype_card _ hmem
      _ = Nat.choose 4 n := by rw [Finset.card_powersetCard,ht4]
  refine ⟨J,K.finiteFaceSpan_finite F,hspace,?_,?_⟩
  · intro a ha
    have hlt := Finset.card_lt_card ((hfaces a).mp ha).2
    omega
  · rw [SimplicialComplex.surfaceEulerCount,hcard 1 (by omega) (by omega),
      hcard 2 (by omega) (by omega),hcard 3 (by omega) (by omega)]
    norm_num [Nat.choose]

end PoincareConjecture.M76.PrismBelt
