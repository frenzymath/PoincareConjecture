import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MatchedRectangleBelt
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalRectangleHeightProduct



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_matched_belt_product
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M W Z : ι → Set E) (L : κ → Set E) (ends : ι → Bool → κ)
    (G : ∀ i, Square ≃ₜ M i) (hG : ∀ i, (G i).IsFinitePL)
    (e : ∀ k, I ≃ₜ L k)
    (hside : ∀ i b t, (G i (sidePoint b t) : E) = e (ends i b) t)
    (hWsub : ∀ i, W i ⊆ M i) (hZsub : ∀ i, Z i ⊆ M i)
    (hW : ∀ i p, (G i p : E) ∈ W i ↔ (p : ℝ × ℝ).2 = 0)
    (hZ : ∀ i p, (G i p : E) ∈ Z i ↔ (p : ℝ × ℝ).2 = 1)
    (hcontact : ∀ i k, i ≠ k → (M i ∩ M k).Nonempty →
      ∃ b c, ends i b = ends k c ∧ M i ∩ M k = L (ends i b)) :
    ∃ H : ((⋃ i, W i) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i), H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ ⋃ i, W i),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i p, (H p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ W i) ∧
      (∀ p, (H p : E) ∈ (⋃ i, W i) ↔ (p : E × ℝ).2 = 0) ∧
      (∀ p, (H p : E) ∈ (⋃ i, Z i) ↔ (p : E × ℝ).2 = 1) ∧
      ∀ (j : ι) (u t : I),
        (H ⟨((G j ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E),t),
          mem_iUnion.mpr ⟨j,(hW j _).mpr rfl⟩,t.property⟩ : E) =
          G j ⟨(u,t),u.property,t.property⟩ := by
  classical
  obtain ⟨A,hA⟩ := exists_matched_rectangle_height M L ends G e hside hcontact
  have hover (i k : ι) (hik : i ≠ k) (hne : (M i ∩ M k).Nonempty) :
      ∃ d : I ≃ₜ (M i ∩ M k : Set E), ∀ t, A (d t) = (t : ℝ) := by
    obtain ⟨b,c,_,hmeet⟩ := hcontact i k hik hne
    let d := (e (ends i b)).trans (Homeomorph.setCongr hmeet.symm)
    refine ⟨d,?_⟩
    intro t
    change A (e (ends i b) t) = (t : ℝ)
    rw [←hside,hA]
    rfl
  have hboundary (i k : ι) (hik : i ≠ k) (p : Square) (hp : (G i p : E) ∈ M k) :
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1 := by
    obtain ⟨b,c,_,hmeet⟩ := hcontact i k hik ⟨G i p,(G i p).property,hp⟩
    have hl := hmeet.subset ⟨(G i p).property,hp⟩
    cases b
    · exact Or.inl ((vertical_side_iff_of_square_chart (G i) (e (ends i false)) 0
        (hside i false) p).mp hl)
    · exact Or.inr ((vertical_side_iff_of_square_chart (G i) (e (ends i true)) 1
        (hside i true) p).mp hl)
  have hlevel (B : ι → Set E) (z : ℝ) (hBsub : ∀ i, B i ⊆ M i)
      (hB : ∀ i p, (G i p : E) ∈ B i ↔ (p : ℝ × ℝ).2 = z) :
      (⋃ i, B i) = (⋃ i, M i) ∩ {x | A x = z} := by
    have hl (i : ι) (x : E) (hx : x ∈ M i) : x ∈ B i ↔ A x = z := by
      have hh := hB i ((G i).symm ⟨x,hx⟩)
      rw [←hA i ((G i).symm ⟨x,hx⟩)] at hh
      simpa only [(G i).apply_symm_apply] using hh
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨i,hBsub i hi⟩,(hl i x (hBsub i hi)).mp hi⟩
    · rintro ⟨hx,hz⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i,(hl i x hi).mpr hz⟩
  have hbottom := hlevel W 0 hWsub hW
  have htop := hlevel Z 1 hZsub hZ
  obtain ⟨H,hH,hHA,hHb,hHm,hformula⟩ :=
    exists_rectangle_height_product_with_all_formulas M A G hG hA hover hboundary
  have hsource : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) = (⋃ i, W i) ×ˢ I := by
    rw [hbottom]
  let J := (Homeomorph.setCongr hsource.symm).trans H
  refine ⟨J,hH.setCongr hsource rfl,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact hHb x (hbottom.subset hx)
  · intro i p
    have hz : A (p : E × ℝ).1 = 0 := (hbottom.subset p.property.1).2
    change (H _ : E) ∈ M i ↔ _
    rw [hHm]
    constructor
    · intro hp
      have hh := hW i ((G i).symm ⟨(p : E × ℝ).1,hp⟩)
      rw [←hA i ((G i).symm ⟨(p : E × ℝ).1,hp⟩)] at hh
      simpa only [(G i).apply_symm_apply,hz,iff_true] using hh
    · intro hp
      exact hWsub i hp
  · intro p
    have hh := Set.ext_iff.mp hbottom (J p : E)
    simp only [mem_inter_iff,mem_ofPred_eq,(J p).property,true_and] at hh
    exact hh.trans ((congrArg (fun t : ℝ => t = 0)
      (hHA ((Homeomorph.setCongr hsource.symm) p))).to_iff)
  · intro p
    have hh := Set.ext_iff.mp htop (J p : E)
    simp only [mem_inter_iff,mem_ofPred_eq,(J p).property,true_and] at hh
    exact hh.trans ((congrArg (fun t : ℝ => t = 1)
      (hHA ((Homeomorph.setCongr hsource.symm) p))).to_iff)
  · intro j u t
    exact hformula j ⟨((G j ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E),t),
      ⟨(G j _).property,hA j _⟩,t.property⟩ u rfl

end PoincareConjecture.M76.PrismBelt
