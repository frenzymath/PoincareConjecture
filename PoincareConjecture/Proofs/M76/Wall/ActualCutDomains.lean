import PoincareConjecture.Proofs.M76.Wall.OppositePLDomain
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceBoundaryPullback











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_original_PL_cut_domains
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hcut : Y ∩ frontier K = F) :
    ∃ d : ι × Y → OpenPartialHomeomorph Y V3,
      PLDomain d ((Subtype.val : Y → X) ⁻¹' K) ∧
      PLDomain d ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) ∧
      (∀ k, MapsTo (Subtype.val : Y → X) (d k).source (e k.1).source) ∧
      (∀ k, (d k).target ⊆ (e k.1).target) ∧
      (∀ k, (d k : Y → V3) = (e k.1) ∘ Subtype.val) ∧
      (∀ k, EqOn ((Subtype.val : Y → X) ∘ (d k).symm)
        (e k.1).symm (d k).target) ∧
      frontier ((Subtype.val : Y → X) ⁻¹' K) = (Subtype.val : Y → X) ⁻¹' F ∧
      frontier ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) =
        (Subtype.val : Y → X) ⁻¹' F ∧
      ((Subtype.val : Y → X) ⁻¹' K) ∪
        ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) = univ ∧
      ((Subtype.val : Y → X) ⁻¹' K) ∩
        ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) =
          (Subtype.val : Y → X) ⁻¹' F ∧
      Disjoint (interior ((Subtype.val : Y → X) ⁻¹' K))
        (interior ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ)) ∧
      interior ((Subtype.val : Y → X) ⁻¹' K) ∪
        interior ((Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) =
          ((Subtype.val : Y → X) ⁻¹' F)ᶜ := by
  let v : Y → X := Subtype.val
  have hv : IsLocalHomeomorph v := hY.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  obtain ⟨d, hdcover, _, hdsource, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hv.exists_piecewiseAffine_coordinate_cover_over e hK.cover hK.compatible
  obtain ⟨hQ, hQfront⟩ := hK.compl_interior
  have hplus : PLDomain d (v ⁻¹' K) :=
    ⟨hdcover, hdcompat, hK.closed.preimage hv.continuous,
      hv.halfspace_boundary_preimage e d Prod.fst hdtarget hdinv hK.halfspace⟩
  have hminus : PLDomain d (v ⁻¹' (interior K)ᶜ) :=
    ⟨hdcover, hdcompat, hQ.closed.preimage hv.continuous,
      hv.halfspace_boundary_preimage e d Prod.fst hdtarget hdinv hQ.halfspace⟩
  have hFpre : v ⁻¹' frontier K = v ⁻¹' F := by
    ext y
    constructor
    · intro hy
      have h : v y ∈ Y ∩ frontier K := ⟨y.property, hy⟩
      rw [hcut] at h
      exact h
    · intro hy
      have h : v y ∈ Y ∩ frontier K := by
        rw [hcut]
        exact hy
      exact h.2
  have hfplus : frontier (v ⁻¹' K) = v ⁻¹' F := by
    rw [← hv.isOpenMap.preimage_frontier_eq_frontier_preimage hv.continuous, hFpre]
  have hfminus : frontier (v ⁻¹' (interior K)ᶜ) = v ⁻¹' F := by
    rw [← hv.isOpenMap.preimage_frontier_eq_frontier_preimage hv.continuous,
      hQfront, hFpre]
  have hunion : (v ⁻¹' K) ∪ (v ⁻¹' (interior K)ᶜ) = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : v y ∈ K
    · exact Or.inl hy
    · exact Or.inr (fun hi => hy (interior_subset hi))
  have hinter : (v ⁻¹' K) ∩ (v ⁻¹' (interior K)ᶜ) = v ⁻¹' F := by
    rw [← preimage_inter, ← hFpre]
    congr 1
    simp only [frontier, hK.closed.closure_eq, sdiff_eq]
  have hdisj : Disjoint (interior (v ⁻¹' K)) (interior (v ⁻¹' (interior K)ᶜ)) := by
    apply Set.disjoint_left.mpr
    intro y hp hm
    have hy : y ∈ v ⁻¹' F := by
      rw [← hinter]
      exact ⟨interior_subset hp, interior_subset hm⟩
    have hyfront : y ∈ frontier (v ⁻¹' K) := by
      rw [hfplus]
      exact hy
    exact Set.disjoint_left.mp disjoint_interior_frontier hp hyfront
  refine ⟨d, hplus, hminus, hdsource, hdtarget, hdval, hdinv,
    hfplus, hfminus, hunion, hinter, hdisj, ?_⟩
  ext y
  constructor
  · rintro (hp | hm) hy
    · have hyfront : y ∈ frontier (v ⁻¹' K) := by
        rw [hfplus]
        exact hy
      exact Set.disjoint_left.mp disjoint_interior_frontier hp hyfront
    · have hyfront : y ∈ frontier (v ⁻¹' (interior K)ᶜ) := by
        rw [hfminus]
        exact hy
      exact Set.disjoint_left.mp disjoint_interior_frontier hm hyfront
  · intro hy
    change y ∉ v ⁻¹' F at hy
    have hside : y ∈ (v ⁻¹' K) ∪ (v ⁻¹' (interior K)ᶜ) := by
      rw [hunion]
      exact mem_univ y
    rcases hside with hp | hm
    · apply Or.inl
      apply (mem_interior_iff_notMem_frontier hp).mpr
      simpa only [hfplus] using hy
    · apply Or.inr
      apply (mem_interior_iff_notMem_frontier hm).mpr
      simpa only [hfminus] using hy

end PoincareConjecture.M76
