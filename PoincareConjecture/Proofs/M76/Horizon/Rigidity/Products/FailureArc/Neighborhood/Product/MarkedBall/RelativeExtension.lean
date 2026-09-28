import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.MarkedBall

theorem exists_relative_ball_extension
    {E F V W D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    {s base top ann rim : Set E} {t Base Top Ann Rim : Set F}
    (hs : IsFinitePLBallPair V s (ann ∪ (base ∪ top)))
    (ht : IsFinitePLBallPair W t (Ann ∪ (Base ∪ Top)))
    (htop : IsFinitePLBallPair D top rim) (hTop : IsFinitePLBallPair D Top Rim)
    (hcontact : top ∩ ann = rim) (hContact : Top ∩ Ann = Rim)
    (hdis : Disjoint top base) (hDis : Disjoint Top Base)
    (b : base ≃ₜ Base) (hb : b.IsFinitePL)
    (a : ann ≃ₜ Ann) (ha : a.IsFinitePL)
    (hoverlap : ∀ x : base, (x : E) ∈ ann ↔ (b x : F) ∈ Ann)
    (hagree : ∀ x (hx : x ∈ base) (hy : x ∈ ann), (b ⟨x,hx⟩ : F) = a ⟨x,hy⟩)
    (hrim : ∀ x : ann, (x : E) ∈ rim ↔ (a x : F) ∈ Rim) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : base, (H ⟨x,hs.1 (Or.inr (Or.inl x.property))⟩ : F) = b x) ∧
      (∀ x : ann, (H ⟨x,hs.1 (Or.inl x.property)⟩ : F) = a x) ∧
      (∀ x : s, (x : E) ∈ top ↔ (H x : F) ∈ Top) ∧
      (∀ x : s, (x : E) ∈ base ↔ (H x : F) ∈ Base) ∧
      ∀ x : s, (x : E) ∈ ann ↔ (H x : F) ∈ Ann := by
  obtain ⟨G,hG,hGb,hGa⟩ := Homeomorph.exists_union_finitePL b a hb ha hoverlap hagree
  have hGann := G.mem_subset_iff_of_extension a subset_union_right subset_union_right
    (fun x ↦ Subtype.ext (hGa x))
  have hmeet : top ∩ (base ∪ ann) = rim := by
    rw [inter_union_distrib_left,hdis.inter_eq,empty_union,hcontact]
  have hMeet : Top ∩ (Base ∪ Ann) = Rim := by
    rw [inter_union_distrib_left,hDis.inter_eq,empty_union,hContact]
  have hmem (x : (base ∪ ann : Set E)) : (x : E) ∈ rim ↔ (G x : F) ∈ Rim := by
    by_cases hx : (x : E) ∈ ann
    · have hv := hGa ⟨x,hx⟩
      change (G x : F) = (a ⟨x,hx⟩ : F) at hv
      rw [hv]
      exact hrim ⟨x,hx⟩
    · have hr : rim ⊆ ann := hcontact.symm.subset.trans inter_subset_right
      have hR : Rim ⊆ Ann := hContact.symm.subset.trans inter_subset_right
      exact iff_of_false (fun h ↦ hx (hr h))
        (fun h ↦ hx ((hGann x).mpr (hR h)))
  obtain ⟨B,hB,hBG,hBtop,_⟩ := htop.exists_union_homeomorph_of_boundary_piece
    hTop hmeet hMeet G hG hmem
  have hsource : top ∪ (base ∪ ann) = ann ∪ (base ∪ top) := by ac_rfl
  have htarget : Top ∪ (Base ∪ Ann) = Ann ∪ (Base ∪ Top) := by ac_rfl
  let C := (Homeomorph.setCongr hsource.symm).trans
    (B.trans (Homeomorph.setCongr htarget))
  have hC : C.IsFinitePL := hB.setCongr hsource htarget
  obtain ⟨H,hH,hHC,_⟩ := hs.exists_extension ht C hC
  have hHb (x : base) : (H ⟨x,hs.1 (Or.inr (Or.inl x.property))⟩ : F) = b x := by
    have h := congrArg Subtype.val (hHC ⟨x,Or.inr (Or.inl x.property)⟩)
    exact h.trans ((congrArg Subtype.val (hBG ⟨x,Or.inl x.property⟩)).trans (hGb x))
  have hHa (x : ann) : (H ⟨x,hs.1 (Or.inl x.property)⟩ : F) = a x := by
    have h := congrArg Subtype.val (hHC ⟨x,Or.inl x.property⟩)
    exact h.trans ((congrArg Subtype.val (hBG ⟨x,Or.inr x.property⟩)).trans (hGa x))
  have htopsub : top ⊆ ann ∪ (base ∪ top) := subset_union_right.trans subset_union_right
  have hTopsub : Top ⊆ Ann ∪ (Base ∪ Top) := subset_union_right.trans subset_union_right
  have hCtop (x : (ann ∪ (base ∪ top) : Set E)) :
      (x : E) ∈ top ↔ (C x : F) ∈ Top := hBtop ⟨x,hsource.symm.subset x.property⟩
  let Ctop := C.restrictSubsets htopsub hTopsub hCtop
  refine ⟨H,hH,hHb,hHa,?_,?_,?_⟩
  · exact H.mem_subset_iff_of_extension Ctop (htopsub.trans hs.1) (hTopsub.trans ht.1)
      (fun x ↦ hHC ⟨x,htopsub x.property⟩)
  · exact H.mem_subset_iff_of_extension b (fun _ hx ↦ hs.1 (Or.inr (Or.inl hx)))
      (fun _ hx ↦ ht.1 (Or.inr (Or.inl hx))) (fun x ↦ Subtype.ext (hHb x))
  · exact H.mem_subset_iff_of_extension a (fun _ hx ↦ hs.1 (Or.inl hx))
      (fun _ hx ↦ ht.1 (Or.inl hx)) (fun x ↦ Subtype.ext (hHa x))

end PoincareConjecture.M76.Dehn.Annuli.MarkedBall
