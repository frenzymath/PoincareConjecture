import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall









set_option autoImplicit false
open Set Geometry

namespace Set

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

private theorem extend_annulus_across_caps
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {band : Set E} {Band : Set F} (caps q : Bool → Set E) (Caps Q : Bool → Set F)
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b) (q b))
    (hCaps : ∀ b, IsFinitePLBallPair P2 (Caps b) (Q b))
    (hmeet : ∀ b, caps b ∩ band = q b) (hMeet : ∀ b, Caps b ∩ Band = Q b)
    (hdis : Disjoint (caps true) (caps false)) (hDis : Disjoint (Caps true) (Caps false))
    (e : band ≃ₜ Band) (he : e.IsFinitePL)
    (hmem : ∀ b (x : band), (x : E) ∈ q b ↔ (e x : F) ∈ Q b) :
    ∃ H : (caps false ∪ (caps true ∪ band) : Set E) ≃ₜ
        (Caps false ∪ (Caps true ∪ Band) : Set F), H.IsFinitePL ∧
      (∀ x : band, (H ⟨x,Or.inr (Or.inr x.property)⟩ : F) = e x) ∧
      ∀ b (x : (caps false ∪ (caps true ∪ band) : Set E)),
        (x : E) ∈ caps b ↔ (H x : F) ∈ Caps b := by
  obtain ⟨G,hG,hkeep,hGcap,hGband⟩ :=
    (hcaps true).exists_union_homeomorph_of_boundary_piece (hCaps true)
      (hmeet true) (hMeet true) e he (hmem true)
  have hqband (b : Bool) : q b ⊆ band := by rw [← hmeet b]; exact inter_subset_right
  have hQband (b : Bool) : Q b ⊆ Band := by rw [← hMeet b]; exact inter_subset_right
  have hinter : caps false ∩ (caps true ∪ band) = q false := by
    rw [inter_union_distrib_left,hdis.symm.inter_eq,empty_union,hmeet false]
  have hInter : Caps false ∩ (Caps true ∪ Band) = Q false := by
    rw [inter_union_distrib_left,hDis.symm.inter_eq,empty_union,hMeet false]
  have hmemG (x : (caps true ∪ band : Set E)) :
      (x : E) ∈ q false ↔ (G x : F) ∈ Q false := by
    by_cases hx : (x : E) ∈ band
    · have hv := congrArg Subtype.val (hkeep ⟨x,hx⟩)
      change (G x : F) = e ⟨x,hx⟩ at hv
      rw [hv]
      exact hmem false ⟨x,hx⟩
    · exact iff_of_false (fun h => hx (hqband false h))
        (fun h => hx ((hGband x).mpr (hQband false h)))
  obtain ⟨H,hH,hHkeep,hHfalse,_⟩ :=
    (hcaps false).exists_union_homeomorph_of_boundary_piece (hCaps false)
      hinter hInter G hG hmemG
  let g := G.restrictSubsets subset_union_left subset_union_left hGcap
  have hkeeptrue (x : caps true) :
      H ⟨x,Or.inr (Or.inl x.property)⟩ = ⟨g x,Or.inr (Or.inl (g x).property)⟩ := by
    apply Subtype.ext
    exact congrArg Subtype.val (hHkeep ⟨x,Or.inl x.property⟩)
  have hHtrue := H.mem_subset_iff_of_extension g
    (subset_union_left.trans subset_union_right)
    (subset_union_left.trans subset_union_right) hkeeptrue
  refine ⟨H,hH,?_,fun b => by cases b; exact hHfalse; exact hHtrue⟩
  intro x
  exact (congrArg Subtype.val (hHkeep ⟨x,Or.inr x.property⟩)).trans
    (congrArg Subtype.val (hkeep x))

theorem IsFinitePLBallPair.exists_product_extending_annulus
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {B band : Set E} (caps q : Bool → Set E)
    (hB : IsFinitePLBallPair M B (band ∪ (caps false ∪ caps true)))
    (hcaps : ∀ b, IsFinitePLBallPair P2 (caps b) (q b))
    (hmeet : ∀ b, caps b ∩ band = q b)
    (hdis : Disjoint (caps true) (caps false))
    (e : band ≃ₜ (q false ×ˢ I : Set (E × ℝ))) (he : e.IsFinitePL)
    (hmem : ∀ b (x : band), (x : E) ∈ q b ↔
      (e x : E × ℝ) ∈ q false ×ˢ {if b then (1 : ℝ) else 0}) :
    ∃ H : B ≃ₜ (caps false ×ˢ I : Set (E × ℝ)), H.IsFinitePL ∧
      (∀ x : band, (H ⟨x,hB.1 (Or.inl x.property)⟩ : E × ℝ) = e x) ∧
      (∀ b (x : B), (x : E) ∈ caps b ↔
        (H x : E × ℝ) ∈ caps false ×ˢ {if b then (1 : ℝ) else 0}) ∧
      ∀ x : B, (x : E) ∈ band ↔ (H x : E × ℝ) ∈ q false ×ˢ I := by
  let Caps := fun b : Bool => caps false ×ˢ {if b then (1 : ℝ) else 0}
  let Q := fun b : Bool => q false ×ˢ {if b then (1 : ℝ) else 0}
  let Band := q false ×ˢ I
  have hCaps (b : Bool) : IsFinitePLBallPair P2 (Caps b) (Q b) :=
    (hcaps false).prod_singleton _
  have hMeet (b : Bool) : Caps b ∩ Band = Q b := by
    ext z
    constructor
    · exact fun hz => ⟨hz.2.1,hz.1.2⟩
    · intro hz
      refine ⟨⟨(hcaps false).1 hz.1,hz.2⟩,hz.1,?_⟩
      rw [show z.2 = if b then (1 : ℝ) else 0 from hz.2]
      cases b <;> norm_num
  have hDis : Disjoint (Caps true) (Caps false) := by
    apply disjoint_left.mpr
    intro z hz ht
    have h1 : z.2 = 1 := hz.2
    have h0 : z.2 = 0 := ht.2
    linarith
  obtain ⟨eb,heb,hekeep,hecaps⟩ :=
    extend_annulus_across_caps caps q Caps Q hcaps hCaps hmeet hMeet hdis hDis e he hmem
  have hsrc : caps false ∪ (caps true ∪ band) = band ∪ (caps false ∪ caps true) := by
    ac_rfl
  have htgt : Caps false ∪ (Caps true ∪ Band) =
      (q false ×ˢ I) ∪ (caps false ×ˢ ({0,1} : Set ℝ)) := by
    ext z
    simp only [Caps,Band,Bool.false_eq_true,if_false,if_true,mem_union,mem_prod,
      mem_insert_iff,mem_singleton_iff]
    tauto
  let eB := (Homeomorph.setCongr hsrc.symm).trans (eb.trans (Homeomorph.setCongr htgt))
  have heB : eB.IsFinitePL := heb.setCongr hsrc htgt
  have hP := (hcaps false).prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨H,hH,hkeep,_⟩ := hB.exists_extension hP eB heB
  have hbandB : band ⊆ B := subset_union_left.trans hB.1
  have hBandP : Band ⊆ caps false ×ˢ I := prod_mono (hcaps false).1 subset_rfl
  have hHkeep (x : band) : (H ⟨x,hbandB x.property⟩ : E × ℝ) = e x :=
    (congrArg Subtype.val (hkeep ⟨x,Or.inl x.property⟩)).trans (hekeep x)
  refine ⟨H,hH,hHkeep,?_,?_⟩
  · intro b
    have hcs : caps b ⊆ band ∪ (caps false ∪ caps true) := by
      cases b
      · exact subset_union_left.trans subset_union_right
      · exact subset_union_right.trans subset_union_right
    have hcT : Caps b ⊆ (q false ×ˢ I) ∪ (caps false ×ˢ ({0,1} : Set ℝ)) := by
      intro x hx
      refine Or.inr ⟨hx.1,?_⟩
      cases b
      · exact Or.inl hx.2
      · exact Or.inr hx.2
    have hbcaps (x : (band ∪ (caps false ∪ caps true) : Set E)) :
        (x : E) ∈ caps b ↔ (eB x : E × ℝ) ∈ Caps b :=
      hecaps b ⟨x,hsrc.symm.subset x.property⟩
    let ec := eB.restrictSubsets hcs hcT hbcaps
    exact H.mem_subset_iff_of_extension ec (hcs.trans hB.1) (hcT.trans hP.1)
      (fun x => hkeep ⟨x,hcs x.property⟩)
  · exact H.mem_subset_iff_of_extension e hbandB hBandP
      (fun x => Subtype.ext (hHkeep x))

end Set
