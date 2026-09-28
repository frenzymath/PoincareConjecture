import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPrismRim
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk











set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem band_rectangle_data
    {q U : Set E} {a b : E} (hU : IsFinitePLBallPair ℝ U {a, b})
    (hab : a ≠ b) (hUq : U ⊆ q) (f : E × ℝ → E)
    (hf : FinitePiecewiseAffineOn f (q ×ˢ I)) (hi : InjOn f (q ×ˢ I))
    (hzero : ∀ x ∈ q, f (x, 0) = x) :
    IsFinitePLBallPair (ℝ × ℝ) (f '' (U ×ˢ I))
        (U ∪ ((f '' ({a, b} ×ˢ I)) ∪ (f '' (U ×ˢ {1})))) ∧
      IsFinitePLBallPair ℝ ((f '' ({a, b} ×ˢ I)) ∪ (f '' (U ×ˢ {1}))) {a, b} ∧
      IsFinitePLBallPair ℝ (f '' (U ×ˢ {1})) {f (a, 1), f (b, 1)} ∧
      IsFinitePLBallPair ℝ ((f '' ({a, b} ×ˢ I)) ∪ U) {f (a, 1), f (b, 1)} := by
  have hrect := hU.prod (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  have hsub : U ×ˢ I ⊆ q ×ˢ I := prod_mono hUq Subset.rfl
  have ha : a ∈ q := hUq (hU.1 (Or.inl rfl))
  have hb : b ∈ q := hUq (hU.1 (Or.inr rfl))
  have hbottom : f '' (U ×ˢ ({0} : Set ℝ)) = U := by
    ext x
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      change t = 0 at ht
      rw [ht, hzero y (hUq hy)]
      exact hy
    · intro hx
      exact ⟨(x, 0), ⟨hx, rfl⟩, hzero x (hUq hx)⟩
  have hfalse := hU.interval_prism_rim_arcs hab (show (0 : ℝ) < 1 from zero_lt_one) false
  have htrue := hU.interval_prism_rim_arcs hab (show (0 : ℝ) < 1 from zero_lt_one) true
  dsimp only at hfalse htrue
  simp only [Bool.false_eq_true, if_false, if_true] at hfalse htrue
  have hside (j : Bool) :
      ({a, b} ×ˢ I) ∪ (U ×ˢ {if j then 0 else 1}) ⊆ q ×ˢ I := by
    rintro x (hx | hx)
    · exact ⟨hUq (hU.1 hx.1), hx.2⟩
    · refine ⟨hUq hx.1, ?_⟩
      have ht : x.2 = if j then 0 else 1 := hx.2
      rw [ht]
      cases j <;> exact ⟨by norm_num, by norm_num⟩
  have htop : U ×ˢ ({1} : Set ℝ) ⊆ q ×ˢ I := by
    intro x hx
    refine ⟨hUq hx.1, ?_⟩
    rw [show x.2 = 1 from hx.2]
    exact ⟨zero_le_one, le_rfl⟩
  have hball := hrect.image_of_subset hf hsub hi
  rw [← hfalse.2.2.1, image_union, hbottom, image_union] at hball
  have hlow := hfalse.2.1.image_of_subset hf (hside false) hi
  have hupp := htrue.2.1.image_of_subset hf (hside true) hi
  have htopBall := htrue.1.image_of_subset hf htop hi
  refine ⟨hball, ?_, ?_, ?_⟩
  · simpa only [image_union, image_pair, hzero a ha, hzero b hb] using hlow
  · simpa only [image_pair] using htopBall
  · simpa only [image_union, hbottom, image_pair] using hupp





theorem IsFinitePLBallPair.boundary_band_complement
    {s q : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    {a b : E} (ha : a ∈ q) (hb : b ∈ q) (hab : a ≠ b)
    (f : E × ℝ → E) (hf : FinitePiecewiseAffineOn f (q ×ˢ I))
    (hi : InjOn f (q ×ˢ I)) (hinside : MapsTo f (q ×ˢ I) s)
    (hzero : ∀ x ∈ q, f (x, 0) = x)
    (hproper : ∀ x ∈ q ×ˢ I, f x ∈ q ↔ x.2 = 0) :
    IsFinitePLBallPair (ℝ × ℝ)
      (s \ ((f '' (q ×ˢ I)) \ (f '' (q ×ˢ {1})))) (f '' (q ×ˢ {1})) := by
  obtain ⟨U, V, hU, hV, hUV, hIV⟩ := hs.exists_boundary_arcs ha hb hab
  have hUq : U ⊆ q := subset_union_left.trans hUV.subset
  have hVq : V ⊆ q := subset_union_right.trans hUV.subset
  let A := f '' (U ×ˢ I)
  let B := f '' (V ×ˢ I)
  let L := f '' ({a, b} ×ˢ I)
  let T := f '' (U ×ˢ ({1} : Set ℝ))
  let Z := f '' (V ×ˢ ({1} : Set ℝ))
  let W := L ∪ T
  let C := s \ (A \ W)
  let J := ({f (a, 1), f (b, 1)} : Set E)
  have hsubU : U ×ˢ I ⊆ q ×ˢ I := prod_mono hUq Subset.rfl
  have hsubV : V ×ˢ I ⊆ q ×ˢ I := prod_mono hVq Subset.rfl
  have hsubL : ({a, b} : Set E) ×ˢ I ⊆ q ×ˢ I :=
    prod_mono (by rintro x (rfl | rfl) <;> assumption) Subset.rfl
  have htopI {X : Set E} (hXq : X ⊆ q) :
      X ×ˢ ({1} : Set ℝ) ⊆ q ×ˢ I := by
    intro x hx
    exact ⟨hXq hx.1, by rw [show x.2 = 1 from hx.2]; exact ⟨zero_le_one, le_rfl⟩⟩
  have hA := band_rectangle_data hU hab hUq f hf hi hzero
  have hB := band_rectangle_data hV hab hVq f hf hi hzero
  have hAs : A ⊆ s := by rintro x ⟨y, hy, rfl⟩; exact hinside (hsubU hy)
  have hBs : B ⊆ s := by rintro x ⟨y, hy, rfl⟩; exact hinside (hsubV hy)
  have hWproper : W \ {a, b} ⊆ s \ q := by
    intro x hx
    have hxA : x ∈ A := hA.1.1 (Or.inr hx.1)
    refine ⟨hAs hxA, ?_⟩
    intro hxq
    obtain ⟨y, hy, rfl⟩ := hxA
    have hy0 := (hproper y (hsubU hy)).mp hxq
    have hval : f y = y.1 := by
      rw [← Prod.eta y, hy0, hzero y.1 (hUq hy.1)]
    rcases hx.1 with hxL | hxT
    · obtain ⟨z, hz, hzf⟩ := hxL
      have he := hi (hsubL hz) (hsubU hy) hzf
      have hyend : y.1 ∈ ({a, b} : Set E) := he ▸ hz.1
      exact hx.2 (hval.symm ▸ hyend)
    · obtain ⟨z, hz, hzf⟩ := hxT
      have he := hi (htopI hUq hz) (hsubU hy) hzf
      have hy1 : y.2 = 1 := by simpa only [he, mem_singleton_iff] using hz.2
      exact zero_ne_one (hy0.symm.trans hy1)
  have hfirst := hs.boundary_attached_disk_complement hA.1 hAs hU hV hA.2.1 hab
    hIV.subset hUV hWproper
  have hC : IsFinitePLBallPair (ℝ × ℝ) C (W ∪ V) := hfirst.1
  have hAC : A ∪ C = s := hfirst.2.1
  have hACinter : A ∩ C = W := hfirst.2.2.1
  have hAB : A ∩ B = L := by
    rw [← hi.image_inter hsubU hsubV]
    apply congrArg (Set.image f)
    ext x
    change (x.1 ∈ U ∧ x.2 ∈ I) ∧ (x.1 ∈ V ∧ x.2 ∈ I) ↔
      x.1 ∈ ({a, b} : Set E) ∧ x.2 ∈ I
    have he := Set.ext_iff.mp hIV x.1
    change (x.1 ∈ U ∧ x.1 ∈ V) ↔ x.1 ∈ ({a, b} : Set E) at he
    tauto
  have hBC : B ⊆ C := by
    intro x hx
    refine ⟨hBs hx, ?_⟩
    rintro ⟨hxA, hxW⟩
    exact hxW (Or.inl (hAB.subset ⟨hxA, hx⟩))
  have hLT : L ∩ T = J := by
    rw [← hi.image_inter hsubL (htopI hUq)]
    have he : (({a, b} : Set E) ×ˢ I) ∩ (U ×ˢ ({1} : Set ℝ)) =
        ({(a, 1), (b, 1)} : Set (E × ℝ)) := by
      ext x
      constructor
      · rintro ⟨hx, hy⟩
        rcases hx.1 with hxa | hxb
        · exact Or.inl (Prod.ext hxa hy.2)
        · exact Or.inr (Prod.ext hxb hy.2)
      · rintro (rfl | rfl)
        · exact ⟨⟨Or.inl rfl, zero_le_one, le_rfl⟩, hU.1 (Or.inl rfl), rfl⟩
        · exact ⟨⟨Or.inr rfl, zero_le_one, le_rfl⟩, hU.1 (Or.inr rfl), rfl⟩
    rw [he, image_pair]
  have hZT : Z ∩ T = J := by
    rw [← hi.image_inter (htopI hVq) (htopI hUq)]
    have he : (V ×ˢ ({1} : Set ℝ)) ∩ (U ×ˢ ({1} : Set ℝ)) =
        ({(a, 1), (b, 1)} : Set (E × ℝ)) := by
      ext x
      constructor
      · rintro ⟨hx, hy⟩
        rcases hIV.subset ⟨hy.1, hx.1⟩ with hxa | hxb
        · exact Or.inl (Prod.ext hxa hx.2)
        · exact Or.inr (Prod.ext hxb hx.2)
      · rintro (rfl | rfl)
        · exact ⟨⟨hV.1 (Or.inl rfl), rfl⟩, hU.1 (Or.inl rfl), rfl⟩
        · exact ⟨⟨hV.1 (Or.inr rfl), rfl⟩, hU.1 (Or.inr rfl), rfl⟩
    rw [he, image_pair]
  have hLZ : L ∩ Z ⊆ J := by
    rintro x ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
    have he := hi (htopI hVq hz) (hsubL hy) hzy
    have hy1 : y.2 = 1 := by simpa only [he, mem_singleton_iff] using hz.2
    rcases hy.1 with hya | hyb
    · exact Or.inl (congrArg f (Prod.ext hya hy1))
    · exact Or.inr (congrArg f (Prod.ext hyb hy1))
  have hVtop {x : E} (hx : x ∈ T ∪ Z) : x ∉ q := by
    rcases hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := hx
      intro hq
      have h0 := (hproper y (htopI hUq hy)).mp hq
      exact zero_ne_one (h0.symm.trans hy.2)
    · obtain ⟨y, hy, rfl⟩ := hx
      intro hq
      have h0 := (hproper y (htopI hVq hy)).mp hq
      exact zero_ne_one (h0.symm.trans hy.2)
  have hBball : IsFinitePLBallPair (ℝ × ℝ) B ((L ∪ V) ∪ Z) := by
    have he : V ∪ (L ∪ Z) = (L ∪ V) ∪ Z := by
      ext x
      simp only [mem_union]
      tauto
    exact he ▸ hB.1
  have hU1rim : L ∪ V ⊆ W ∪ V := by
    rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hU1T : (L ∪ V) ∩ T ⊆ J := by
    rintro x ⟨hx | hx, hxT⟩
    · exact hLT.subset ⟨hx, hxT⟩
    · exact False.elim (hVtop (Or.inl hxT) (hVq hx))
  have hrim : (L ∪ V) ∪ T = W ∪ V := by
    ext x
    simp only [W, mem_union]
    tauto
  have hab1 : f (a, 1) ≠ f (b, 1) := by
    intro he
    exact hab (congrArg Prod.fst (hi ⟨ha, zero_le_one, le_rfl⟩
      ⟨hb, zero_le_one, le_rfl⟩ he))
  have hZproper : Z \ J ⊆ C \ (W ∪ V) := by
    intro x hx
    have hxB : x ∈ B := hBball.1 (Or.inr hx.1)
    refine ⟨hBC hxB, ?_⟩
    rintro ((hxL | hxT) | hxV)
    · exact hx.2 (hLZ ⟨hxL, hx.1⟩)
    · exact hx.2 (hZT.subset ⟨hx.1, hxT⟩)
    · exact hVtop (Or.inr hx.1) (hVq hxV)
  have hsecond := hC.boundary_attached_disk_complement hBball hBC hB.2.2.2 hA.2.2.1
    hB.2.2.1 hab1 hU1T hrim hZproper
  let C' := C \ (B \ Z)
  have hC' : IsFinitePLBallPair (ℝ × ℝ) C' (Z ∪ T) := hsecond.1
  have hBC' : B ∪ C' = C := hsecond.2.1
  have hBinter : B ∩ C' = Z := hsecond.2.2.1
  have hTC' : T ⊆ C' := by
    intro x hx
    refine ⟨hACinter.symm.subset (Or.inr hx) |>.2, ?_⟩
    rintro ⟨hxB, hxZ⟩
    have hxL := hAB.subset ⟨hA.1.1 (Or.inr (Or.inr hx)), hxB⟩
    have hxJ := hLT.subset ⟨hxL, hx⟩
    exact hxZ (hZT.symm.subset hxJ).1
  have hUnion : (A ∪ B) ∪ C' = s := by rw [union_assoc, hBC', hAC]
  have hInter : (A ∪ B) ∩ C' = T ∪ Z := by
    apply Subset.antisymm
    · rintro x ⟨hx | hx, hxC'⟩
      · have hxW := hACinter.subset ⟨hx, hxC'.1⟩
        rcases hxW with hxL | hxT
        · exact Or.inr (hBinter.subset ⟨hAB.symm.subset hxL |>.2, hxC'⟩)
        · exact Or.inl hxT
      · exact Or.inr (hBinter.subset ⟨hx, hxC'⟩)
    · rintro x (hx | hx)
      · exact ⟨Or.inl (hA.1.1 (Or.inr (Or.inr hx))), hTC' hx⟩
      · exact ⟨Or.inr (hBball.1 (Or.inr hx)), hBinter.symm.subset hx |>.2⟩
  have hband : A ∪ B = f '' (q ×ˢ I) := by
    rw [← image_union, ← union_prod, hUV]
  have htop : T ∪ Z = f '' (q ×ˢ ({1} : Set ℝ)) := by
    rw [← image_union, ← union_prod, hUV]
  have hactual : C' = s \ ((A ∪ B) \ (T ∪ Z)) := by
    ext x
    have hu := Set.ext_iff.mp hUnion x
    have hi' := Set.ext_iff.mp hInter x
    change ((x ∈ A ∨ x ∈ B) ∨ x ∈ C') ↔ x ∈ s at hu
    change ((x ∈ A ∨ x ∈ B) ∧ x ∈ C') ↔ x ∈ T ∪ Z at hi'
    change x ∈ C' ↔ x ∈ s ∧ ¬ (x ∈ A ∪ B ∧ x ∉ T ∪ Z)
    simp only [mem_union] at hi' ⊢
    tauto
  have hpair : IsFinitePLBallPair (ℝ × ℝ) C' (T ∪ Z) := by
    simpa only [union_comm] using hC'
  rwa [hactual, hband, htop] at hpair

end Set
