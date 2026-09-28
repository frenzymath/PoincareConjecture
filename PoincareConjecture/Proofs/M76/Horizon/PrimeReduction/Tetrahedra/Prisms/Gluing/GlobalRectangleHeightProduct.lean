import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.RelativeRectangleHeightProduct
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_rectangle_height_product_with_all_formulas
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (M : ι → Set E) (A : E → ℝ) (G : ∀ i, Square ≃ₜ M i)
    (hG : ∀ i, (G i).IsFinitePL)
    (hheight : ∀ i p, A (G i p) = (p : ℝ × ℝ).2)
    (hover : ∀ i k, i ≠ k → (M i ∩ M k).Nonempty →
      ∃ d : I ≃ₜ (M i ∩ M k : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i k, i ≠ k → ∀ p, (G i p : E) ∈ M k →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1) :
    ∃ H : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) ≃ₜ (⋃ i, M i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ (⋃ i, M i) ∩ {x | A x = 0}),
        (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
      (∀ i p, (H p : E) ∈ M i ↔ (p : E × ℝ).1 ∈ M i) ∧
      ∀ i (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) (u : I),
        (G i ⟨(u,0),u.property,le_rfl,zero_le_one⟩ : E) = (p : E × ℝ).1 →
        (H ⟨p,⟨mem_iUnion.mpr ⟨i,p.property.1.1⟩,p.property.1.2⟩,p.property.2⟩ : E) =
          G i ⟨(u,(p : E × ℝ).2),u.property,p.property.2⟩ := by
  classical
  choose J hJ hJA hJb hJm hJformula using fun i =>
    exists_rectangle_height_product_with_patch_formula M A G hG hheight hover hboundary i
  have hsub (i : ι) : (M i ∩ {x | A x = 0}) ×ˢ I ⊆
      ((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I := by
    exact fun z hz => ⟨⟨mem_iUnion.mpr ⟨i,hz.1.1⟩,hz.1.2⟩,hz.2⟩
  have hMi (i : ι) : M i ⊆ ⋃ i, M i := subset_iUnion M i
  have hmem (i : ι) (z : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      (z : E × ℝ) ∈ (M i ∩ {x | A x = 0}) ×ˢ I ↔ (J i z : E) ∈ M i := by
    exact ((and_iff_left z.property.2).trans (and_iff_left z.property.1.2)).trans (hJm i i z).symm
  let C (i : ι) := (J i).restrictSubsets (hsub i) (hMi i) (hmem i)
  have hC (i : ι) : (C i).IsFinitePL := by
    obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := (hG i).symm
    exact (hJ i).restrictSubsets_of_target (hsub i) (hMi i) (hmem i) K hK hKs
  have hCA (i : ι) (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      A (C i p) = (p : E × ℝ).2 := hJA i _
  have hCb (i : ι) (x : E) (hx : x ∈ M i ∩ {x | A x = 0}) :
      (C i ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x :=
    hJb i x ⟨mem_iUnion.mpr ⟨i,hx.1⟩,hx.2⟩
  have hCm (i k : ι) (p : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ))) :
      (C i p : E) ∈ M k ↔ (p : E × ℝ).1 ∈ M k := hJm i k _
  have hinj (i k : ι) (hik : i ≠ k) : InjOn A (M i ∩ M k) := by
    intro x hx y hy hxy
    obtain ⟨d,hd⟩ := hover i k hik ⟨x,hx⟩
    have hx' : A x = (d.symm ⟨x,hx⟩ : ℝ) := by
      simpa only [d.apply_symm_apply] using hd (d.symm ⟨x,hx⟩)
    have hy' : A y = (d.symm ⟨y,hy⟩ : ℝ) := by
      simpa only [d.apply_symm_apply] using hd (d.symm ⟨y,hy⟩)
    exact congrArg Subtype.val (d.symm.injective (Subtype.ext (hx'.symm.trans (hxy.trans hy'))))
  obtain ⟨H,hH,hHA,hHb,hres⟩ :=
    Homeomorph.exists_iUnion_height_product M A zero_le_one C hC hCA hCb hCm hinj
  refine ⟨H,hH,hHA,hHb,?_,?_⟩
  · intro i p
    constructor
    · intro hp
      let q := (C i).symm ⟨H p,hp⟩
      let q' : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
        ⟨q,⟨mem_iUnion.mpr ⟨i,q.property.1.1⟩,q.property.1.2⟩,q.property.2⟩
      have he : H q' = H p := Subtype.ext ((hres i q).trans
        (congrArg Subtype.val ((C i).apply_symm_apply _)))
      have hv := congrArg (fun z : (((⋃ i, M i) ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) =>
        (z : E × ℝ).1) (H.injective he)
      exact hv ▸ q.property.1.1
    · intro hp
      let q : ((M i ∩ {x | A x = 0}) ×ˢ I : Set (E × ℝ)) :=
        ⟨p,⟨hp,p.property.1.2⟩,p.property.2⟩
      exact (hres i q).symm ▸ (C i q).property
  · intro i p u hu
    exact (hres i p).trans (hJformula i p u hu)

end PoincareConjecture.M76.PrismBelt
