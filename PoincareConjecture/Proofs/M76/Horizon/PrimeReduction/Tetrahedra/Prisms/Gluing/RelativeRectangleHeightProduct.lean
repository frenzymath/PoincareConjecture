import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MarkedRectangleGluing










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_relative_rectangle_height_product
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M : ι → Set E) (A : E → ℝ) (G : ∀ i, Square ≃ₜ M i)
    (hG : ∀ i, (G i).IsFinitePL)
    (hheight : ∀ i p, A (G i p) = (p : ℝ × ℝ).2)
    (hover : ∀ i j, i ≠ j → (M i ∩ M j).Nonempty →
      ∃ d : I ≃ₜ (M i ∩ M j : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i j, i ≠ j → ∀ p, (G i p : E) ∈ M j →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1)
    (j : ι) (J : ((M j ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ M j)
    (hJ : J.IsFinitePL) (hJA : ∀ p, A (J p) = (p : E × ℝ).2)
    (hJbase : ∀ (x : E) (hx : x ∈ M j ∩ {x | A x = 0}),
      (J ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x)
    (hJmem : ∀ i p, (J p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i) :
    ∃ H : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ (⋃ i, M i) ∩ {x | A x = 0}),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i p, (H p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i) ∧
      ∀ p : ((M j ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)),
        (H ⟨p,⟨mem_iUnion.mpr ⟨j,p.property.1.1⟩,p.property.1.2⟩,p.property.2⟩ : E) = J p := by
  classical
  have hex (i : ι) := (hG i).exists_bottom_normalized_rectangle_chart_with_overlaps
    zero_lt_one A (hheight i) (fun k : {k : ι // i ≠ k} => M k.val)
      (fun k => hover i k.val k.property) (fun k => hboundary i k.val k.property)
  choose C hC hCA hbase hmem using hex
  let D (i : ι) : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ M i :=
    if h : i = j then h.symm ▸ J else C i
  have hD (i : ι) : (D i).IsFinitePL := by
    by_cases hi : i = j
    · subst i
      simpa only [D,dif_pos rfl] using hJ
    · simpa only [D,dif_neg hi] using hC i
  have hDA (i : ι) (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      A (D i p) = (p : E × ℝ).2 := by
    by_cases hi : i = j
    · subst i
      simpa only [D,dif_pos rfl] using hJA p
    · simpa only [D,dif_neg hi] using hCA i p
  have hDb (i : ι) (x : E) (hx : x ∈ M i ∩ {x | A x = 0}) :
      (D i ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x := by
    by_cases hi : i = j
    · subst i
      simpa only [D,dif_pos rfl] using hJbase x hx
    · simpa only [D,dif_neg hi] using hbase i x hx
  have hDm (i k : ι) (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      (D i p : E) ∈ M k ↔ (p : E × ℝ).1 ∈ M k := by
    by_cases hi : i = j
    · subst i
      simpa only [D,dif_pos rfl] using hJmem k p
    · simp only [D,dif_neg hi]
      by_cases hik : i = k
      · subst k
        exact iff_of_true (C i p).property p.property.1.1
      · exact hmem i ⟨k,hik⟩ p
  have hinj (i k : ι) (hik : i ≠ k) : InjOn A (M i ∩ M k) := by
    intro x hx y hy hxy
    obtain ⟨d,hd⟩ := hover i k hik ⟨x,hx⟩
    have he : d.symm ⟨x,hx⟩ = d.symm ⟨y,hy⟩ := by
      apply Subtype.ext
      have hx' : A x = (d.symm ⟨x,hx⟩ : ℝ) := by
        simpa only [d.apply_symm_apply] using hd (d.symm ⟨x,hx⟩)
      have hy' : A y = (d.symm ⟨y,hy⟩ : ℝ) := by
        simpa only [d.apply_symm_apply] using hd (d.symm ⟨y,hy⟩)
      exact hx'.symm.trans (hxy.trans hy')
    exact congrArg Subtype.val (d.symm.injective he)
  obtain ⟨H,hH,hHA,hHb,hres⟩ :=
    Homeomorph.exists_iUnion_height_product M A zero_le_one D hD hDA hDb hDm hinj
  refine ⟨H,hH,hHA,hHb,?_,?_⟩
  · intro i p
    constructor
    · intro hp
      let q := (D i).symm ⟨H p,hp⟩
      let q' : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
        ⟨q,⟨mem_iUnion.mpr ⟨i,q.property.1.1⟩,q.property.1.2⟩,q.property.2⟩
      have he : H q' = H p := Subtype.ext ((hres i q).trans
        (congrArg Subtype.val ((D i).apply_symm_apply _)))
      have hqp := congrArg (fun z : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) =>
        (z : E × ℝ).1) (H.injective he)
      exact hqp ▸ q.property.1.1
    · intro hp
      let q : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
        ⟨p,⟨hp,p.property.1.2⟩,p.property.2⟩
      exact (hres i q).symm ▸ (D i q).property
  · intro p
    simpa only [D,dif_pos rfl] using hres j p

theorem exists_rectangle_height_product_with_patch_formula
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M : ι → Set E) (A : E → ℝ) (G : ∀ i, Square ≃ₜ M i)
    (hG : ∀ i, (G i).IsFinitePL)
    (hheight : ∀ i p, A (G i p) = (p : ℝ × ℝ).2)
    (hover : ∀ i k, i ≠ k → (M i ∩ M k).Nonempty →
      ∃ d : I ≃ₜ (M i ∩ M k : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i k, i ≠ k → ∀ p, (G i p : E) ∈ M k →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1)
    (j : ι) :
    ∃ H : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ (⋃ i, M i) ∩ {x | A x = 0}),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i p, (H p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i) ∧
      ∀ (p : ((M j ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) (u : I),
        (G j ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E) = (p : E × ℝ).1 →
        (H ⟨p,⟨mem_iUnion.mpr ⟨j,p.property.1.1⟩,p.property.1.2⟩,p.property.2⟩ : E) =
          G j ⟨(u,(p : E × ℝ).2),u.property,p.property.2⟩ := by
  obtain ⟨J,hJ,hJA,hJbase,hformula⟩ :=
    (hG j).exists_bottom_normalized_rectangle_chart zero_lt_one A (hheight j)
  have hJmem (i : ι) (p : ((M j ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      (J p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i := by
    by_cases hji : j = i
    · subst i
      exact iff_of_true (J p).property p.property.1.1
    by_cases hmeet : (M j ∩ M i).Nonempty
    · obtain ⟨d,hd⟩ := hover j i hji hmeet
      obtain ⟨k,_,hk⟩ := Homeomorph.exists_rectangle_side_of_height_interval zero_le_one
        (G j) d inter_subset_left A (hheight j) hd (fun t => by
          apply hboundary j i hji
          simpa only [(G j).apply_symm_apply] using (d t).property.2)
      let p₀ := (G j).symm ⟨(p : E × ℝ).1,p.property.1.1⟩
      have hp₀ : (G j p₀ : E) = (p : E × ℝ).1 :=
        congrArg Subtype.val ((G j).apply_symm_apply _)
      have ht : (p₀ : ℝ × ℝ).2 = 0 :=
        (hheight j p₀).symm.trans ((congrArg A hp₀).trans p.property.1.2)
      let u : I := ⟨(p₀ : ℝ × ℝ).1,p₀.property.1⟩
      have hu : (G j ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E) =
          (p : E × ℝ).1 := by
        convert hp₀ using 1
        exact congrArg (fun z : Square => (G j z : E)) (Subtype.ext (Prod.ext rfl ht.symm))
      have hs := Homeomorph.rectangle_side_mem_iff (G j) k d hk
      have h₁ := hs (⟨(u,(p : E × ℝ).2),u.property,p.property.2⟩ : Square)
      have h₀ := hs (⟨(u,0),u.property,le_rfl,zero_le_one⟩ : Square)
      rw [hformula p u hu]
      have hmem : (G j ⟨(u,(p : E × ℝ).2),u.property,p.property.2⟩ : E) ∈ M j ∩ M i ↔
          (G j ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E) ∈ M j ∩ M i := h₁.trans h₀.symm
      simpa only [mem_inter_iff,(G j _).property,true_and,hu,p.property.1.1] using hmem
    · exact iff_of_false (fun hi => hmeet ⟨J p,(J p).property,hi⟩)
        (fun hi => hmeet ⟨(p : E × ℝ).1,p.property.1.1,hi⟩)
  obtain ⟨H,hH,hHA,hHb,hHm,hres⟩ := exists_relative_rectangle_height_product
    M A G hG hheight hover hboundary j J hJ hJA hJbase hJmem
  exact ⟨H,hH,hHA,hHb,hHm,fun p u hu => (hres p).trans (hformula p u hu)⟩

end PoincareConjecture.M76.PrismBelt
