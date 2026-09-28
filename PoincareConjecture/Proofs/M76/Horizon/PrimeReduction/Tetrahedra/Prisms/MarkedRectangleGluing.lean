import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MatchedRectangleHeight

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PrismBelt

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_marked_rectangle_height_product
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M : ι → Set E) (A : E → ℝ) (G : ∀ i, Square ≃ₜ M i)
    (hG : ∀ i, (G i).IsFinitePL)
    (hheight : ∀ i p, A (G i p) = (p : ℝ × ℝ).2)
    (hover : ∀ i j, i ≠ j → (M i ∩ M j).Nonempty →
      ∃ d : I ≃ₜ (M i ∩ M j : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i j, i ≠ j → ∀ p, (G i p : E) ∈ M j →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1) :
    ∃ H : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ (⋃ i, M i) ∩ {x | A x = 0}),
        (H ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x) ∧
      ∀ i p, (H p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i := by
  classical
  have hex (i : ι) := (hG i).exists_bottom_normalized_rectangle_chart_with_overlaps
    zero_lt_one A (hheight i) (fun j : {j : ι // i ≠ j} => M j.val)
      (fun j => hover i j.val j.property) (fun j => hboundary i j.val j.property)
  choose C hC hCA hbase hmem using hex
  have hoverlap (i j : ι) (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      (C i p : E) ∈ M j ↔ (p : E × ℝ).1 ∈ M j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true (C i p).property p.property.1.1
    · exact hmem i ⟨j, hij⟩ p
  have hinj (i j : ι) (hij : i ≠ j) : InjOn A (M i ∩ M j) := by
    intro x hx y hy hxy
    obtain ⟨d, hd⟩ := hover i j hij ⟨x, hx⟩
    let t := d.symm ⟨x, hx⟩
    let s := d.symm ⟨y, hy⟩
    have ht : (d t : E) = x := congrArg Subtype.val (d.apply_symm_apply _)
    have hs : (d s : E) = y := congrArg Subtype.val (d.apply_symm_apply _)
    have hts : t = s := Subtype.ext
      ((hd t).symm.trans ((congrArg A ht).trans
        (hxy.trans ((congrArg A hs).symm.trans (hd s)))))
    exact ht.symm.trans ((congrArg (fun u => (d u : E)) hts).trans hs)
  obtain ⟨H, hH, hHA, hbottom, hres⟩ :=
    Homeomorph.exists_iUnion_height_product M A zero_le_one C hC hCA hbase hoverlap hinj
  refine ⟨H, hH, hHA, hbottom, ?_⟩
  intro i p
  constructor
  · intro hp
    let q := (C i).symm ⟨H p, hp⟩
    let q' : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
      ⟨q, ⟨⟨mem_iUnion.mpr ⟨i, q.property.1.1⟩, q.property.1.2⟩, q.property.2⟩⟩
    have he : H q' = H p := Subtype.ext ((hres i q).trans
      (congrArg Subtype.val ((C i).apply_symm_apply _)))
    have hqp := congrArg (fun z : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) =>
      (z : E × ℝ).1) (H.injective he)
    exact hqp ▸ q.property.1.1
  · intro hp
    let q : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
      ⟨p, ⟨⟨hp, p.property.1.2⟩, p.property.2⟩⟩
    have he : (H p : E) = C i q := hres i q
    exact he.symm ▸ (C i q).property

end PoincareConjecture.M76.PrismBelt
