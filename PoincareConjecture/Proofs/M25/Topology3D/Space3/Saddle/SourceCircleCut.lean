import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCirclePairComplement
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose








set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_source_circle_cut
    (n : ℕ) (q : Fin n → UnitCircle → UnitTwoSphere)
    (hq : ∀ j : Fin n,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q j) ∧
      Function.Injective (q j) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q j) theta))
    (hdisjoint : ∀ i j : Fin n, i ≠ j → Disjoint (range (q i)) (range (q j)))
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (hgamma : ∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i))
    (hgdisjoint : Disjoint (range (gamma 0)) (range (gamma 1)))
    (p : Fin 4 → UnitTwoSphere)
    (hend : ∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))))
    (V C : Set UnitTwoSphere)
    (hclosed : (⋃ j : Fin n, range (q j)) ∩ C = ⋃ i : Fin 2, range (gamma i))
    (hopen : (⋃ j : Fin n, range (q j)) ∩ V =
      ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1) :
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let Sigma : Set UnitTwoSphere := ⋃ j : Fin n, range (q j)
    ∃ (removedParent arcParent : Fin 2 → Fin n)
      (a v : Fin 2 → ℝ) (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ),
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (arcParent k)
        (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    let bypass : Finset (Fin n) :=
      Finset.univ \ {removedParent 0, removedParent 1}
    Function.Injective p ∧ 0 < eta ∧ eta < 1 / 8 ∧
    (∀ i : Fin 2, range (gamma i) ⊆ range (q (removedParent i))) ∧
    (∀ k : Fin 2,
      0 < |v k| ∧ |v k| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha k) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha k) t)) ∧
      Set.InjOn (alpha k) (Icc (-eta) (1 + eta)) ∧
      alpha k 0 = p (ends (k, 0)) ∧
      alpha k 1 = p (ends (k, 1)) ∧
      Disjoint (alpha k '' Ioo (0 : ℝ) 1) C ∧
      (alpha k '' Icc (0 : ℝ) 1) ∩ C =
        {p (ends (k, 0)), p (ends (k, 1))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), alpha k s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), alpha k s ∈ V)) ∧
    Disjoint (alpha 0 '' Icc (-eta) (1 + eta))
      (alpha 1 '' Icc (-eta) (1 + eta)) ∧
    (∀ k : Fin 2, ∀ j ∈ bypass,
      Disjoint (alpha k '' Icc (0 : ℝ) 1) (range (q j))) ∧
    (∀ j : Fin n, j ∈ bypass ↔ Disjoint (range (q j)) C) ∧
    Sigma \ V = (⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1) ∪
      (⋃ j ∈ bypass, range (q j)) ∧
    Sigma ∩ (C \ V) = range p ∧
    bypass.card + (if removedParent 0 = removedParent 1 then 1 else 2) = n ∧
    (removedParent 0 ≠ removedParent 1 →
      arcParent = removedParent ∧
      ∀ k : Fin 2,
        ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) = {ep (k, 0), ep (k, 1)}) ∧
    (removedParent 0 = removedParent 1 →
      (∀ k : Fin 2, arcParent k = removedParent 0) ∧
      ∀ k : Fin 2,
        (ep.symm (ends (k, 0))).1 ≠ (ep.symm (ends (k, 1))).1) := by
  classical
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let Sigma : Set UnitTwoSphere := ⋃ j : Fin n, range (q j)
  have hqSigma (j : Fin n) : range (q j) ⊆ Sigma := fun _ hy => mem_iUnion.mpr ⟨j, hy⟩
  have hgSigma (i : Fin 2) : range (gamma i) ⊆ Sigma := by
    intro y hy
    have hh : y ∈ ⋃ k : Fin 2, range (gamma k) := mem_iUnion.mpr ⟨i, hy⟩
    rw [← hclosed] at hh
    exact hh.1
  have hgC (i : Fin 2) : range (gamma i) ⊆ C := by
    intro y hy
    have hh : y ∈ ⋃ k : Fin 2, range (gamma k) := mem_iUnion.mpr ⟨i, hy⟩
    rw [← hclosed] at hh
    exact hh.2
  have hgV (i : Fin 2) : gamma i '' Ioo (0 : unitInterval) 1 ⊆ V := by
    intro y hy
    have hh : y ∈ ⋃ k : Fin 2, gamma k '' Ioo (0 : unitInterval) 1 := mem_iUnion.mpr ⟨i, hy⟩
    rw [← hopen] at hh
    exact hh.2
  have hmemC (y : UnitTwoSphere) (hy : y ∈ Sigma) :
      y ∈ C ↔ ∃ i : Fin 2, y ∈ range (gamma i) := by
    constructor
    · intro hc
      apply mem_iUnion.mp
      rw [← hclosed]
      exact ⟨hy, hc⟩
    · rintro ⟨i, hi⟩
      exact hgC i hi
  have hmemV (y : UnitTwoSphere) (hy : y ∈ Sigma) :
      y ∈ V ↔ ∃ i : Fin 2, y ∈ gamma i '' Ioo (0 : unitInterval) 1 := by
    constructor
    · intro hv
      apply mem_iUnion.mp
      rw [← hopen]
      exact ⟨hy, hv⟩
    · rintro ⟨i, hi⟩
      exact hgV i hi
  have hgp (i j : Fin 2) (hij : i ≠ j) : Disjoint (range (gamma i)) (range (gamma j)) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hgdisjoint
    · exact hgdisjoint.symm
    · exact False.elim (hij rfl)
  have hparents (i : Fin 2) : ∃ j : Fin n, range (gamma i) ⊆ range (q j) := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hgSigma i ⟨0, rfl⟩)
    let Other : Set UnitTwoSphere := ⋃ k : {k : Fin n // k ≠ j}, range (q k)
    have hOther : IsClosed Other := isClosed_iUnion_of_finite
      (fun k => (isCompact_range (hq k).1.continuous).isClosed)
    have hqd : Disjoint (range (q j)) Other := by
      apply Set.disjoint_left.mpr
      intro y hy hh
      obtain ⟨k, hk⟩ := mem_iUnion.mp hh
      exact Set.disjoint_left.mp (hdisjoint j k k.property.symm) hy hk
    have hcover : Sigma ⊆ range (q j) ∪ Other := by
      intro y hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      by_cases hkj : k = j
      · exact Or.inl (hkj ▸ hk)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩)
    have hp := (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_range (hgamma i).1)) (range (q j)) Other
      (isCompact_range (hq j).1.continuous).isClosed hOther ((hgSigma i).trans hcover)
      (by rw [hqd.inter_eq, inter_empty])
    rcases hp with hp | hp
    · exact ⟨j, hp⟩
    · exact False.elim (Set.disjoint_left.mp hqd hj (hp ⟨0, rfl⟩))
  choose removedParent hparent using hparents
  let bypass : Finset (Fin n) := Finset.univ \ {removedParent 0, removedParent 1}
  have hbmem (j : Fin n) : j ∈ bypass ↔ j ≠ removedParent 0 ∧ j ≠ removedParent 1 := by
    simp [bypass, not_or]
  have hnotparent (i : Fin 2) (j : Fin n) (hj : j ∈ bypass) : removedParent i ≠ j := by
    have hh := (hbmem j).mp hj
    fin_cases i
    · exact hh.1.symm
    · exact hh.2.symm
  have hbiff (j : Fin n) : j ∈ bypass ↔ Disjoint (range (q j)) C := by
    constructor
    · intro hj
      apply Set.disjoint_left.mpr
      intro y hy hc
      obtain ⟨i, hi⟩ := (hmemC y (hqSigma j hy)).mp hc
      exact Set.disjoint_left.mp (hdisjoint j (removedParent i) (hnotparent i j hj).symm)
        hy (hparent i hi)
    · intro hj
      apply (hbmem j).mpr
      constructor <;> intro heq
      · exact Set.disjoint_left.mp hj (heq.symm ▸ hparent 0 ⟨0, rfl⟩) (hgC 0 ⟨0, rfl⟩)
      · exact Set.disjoint_left.mp hj (heq.symm ▸ hparent 1 ⟨0, rfl⟩) (hgC 1 ⟨0, rfl⟩)
  have hbext (j : Fin n) (hj : j ∈ bypass) : range (q j) ⊆ Sigma \ V := by
    intro y hy
    refine ⟨hqSigma j hy, ?_⟩
    intro hv
    obtain ⟨i, t, ht, hty⟩ := (hmemV y (hqSigma j hy)).mp hv
    exact Set.disjoint_left.mp ((hbiff j).mp hj) hy (hgC i ⟨t, hty⟩)
  have hcard : bypass.card + (if removedParent 0 = removedParent 1 then 1 else 2) = n := by
    have hh := Finset.card_sdiff_add_card_eq_card
      (show ({removedParent 0, removedParent 1} : Finset (Fin n)) ⊆ Finset.univ from
        Finset.subset_univ _)
    by_cases heq : removedParent 0 = removedParent 1
    · simpa [bypass, heq] using hh
    · simpa [bypass, heq, Finset.card_pair heq] using hh
  let endpoint : Fin 2 → unitInterval := ![0, 1]
  have hendpoint : Injective endpoint := by
    intro e f hef
    fin_cases e <;> fin_cases f <;> try rfl
    · have h : (0 : unitInterval) = 1 := hef
      exact False.elim (zero_ne_one h)
    · have h : (1 : unitInterval) = 0 := hef
      exact False.elim (one_ne_zero h)
  have hpairs (i e : Fin 2) : p (ep (i, e)) = gamma i (endpoint e) := by
    fin_cases e
    · exact (hend i).1.symm
    · exact (hend i).2.symm
  have hpi : Injective p := by
    intro x y hxy
    obtain ⟨⟨i, e⟩, rfl⟩ := ep.surjective x
    obtain ⟨⟨j, f⟩, rfl⟩ := ep.surjective y
    rw [hpairs, hpairs] at hxy
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hgp i j hne) ⟨endpoint e, rfl⟩ ⟨endpoint f, hxy.symm⟩
    subst j
    have hef := hendpoint ((hgamma i).2 hxy)
    subst f
    rfl
  have hendnotV (i : Fin 2) (s : unitInterval) (hs : s = 0 ∨ s = 1) : gamma i s ∉ V := by
    intro hv
    obtain ⟨j, t, ht, hts⟩ := (hmemV _ (hgSigma i ⟨s, rfl⟩)).mp hv
    by_cases hji : j = i
    · subst j
      have hh := (hgamma i).2 hts
      subst t
      rcases hs with rfl | rfl <;> simp at ht
    · exact Set.disjoint_left.mp (hgp j i hji) ⟨t, hts⟩ ⟨s, rfl⟩
  have hboundary : Sigma ∩ (C \ V) = range p := by
    ext y
    constructor
    · rintro ⟨hyS, hyC, hyV⟩
      obtain ⟨i, s, hsy⟩ := (hmemC y hyS).mp hyC
      by_cases hs0 : s = 0
      · exact ⟨ep (i, 0), (hend i).1.symm.trans (hs0 ▸ hsy)⟩
      by_cases hs1 : s = 1
      · exact ⟨ep (i, 1), (hend i).2.symm.trans (hs1 ▸ hsy)⟩
      exact False.elim (hyV (hgV i ⟨s, ⟨unitInterval.pos_iff_ne_zero.mpr hs0,
        unitInterval.lt_one_iff_ne_one.mpr hs1⟩, hsy⟩))
    · rintro ⟨k, rfl⟩
      obtain ⟨⟨i, e⟩, rfl⟩ := ep.surjective k
      fin_cases e
      · change p (ep (i, 0)) ∈ Sigma ∩ (C \ V)
        rw [hpairs]
        change gamma i 0 ∈ Sigma ∩ (C \ V)
        exact ⟨hgSigma i ⟨0, rfl⟩, hgC i ⟨0, rfl⟩, hendnotV i 0 (Or.inl rfl)⟩
      · change p (ep (i, 1)) ∈ Sigma ∩ (C \ V)
        rw [hpairs]
        change gamma i 1 ∈ Sigma ∩ (C \ V)
        exact ⟨hgSigma i ⟨1, rfl⟩, hgC i ⟨1, rfl⟩, hendnotV i 1 (Or.inr rfl)⟩
  have hsmooth (j : Fin n) (a v : ℝ) (hv : v ≠ 0) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞
        (fun t : ℝ => q j (complexUnitCircleHomeomorph (Circle.exp (a + v * t)))) ∧
      ∀ t : ℝ, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
        (fun s : ℝ => q j (complexUnitCircleHomeomorph (Circle.exp (a + v * s)))) t) := by
    obtain ⟨ha, hai⟩ := circleAffine_smooth_immersion a v hv
    refine ⟨(hq j).1.comp ha, ?_⟩
    intro t
    change Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      (q j ∘ fun s : ℝ => complexUnitCircleHomeomorph (Circle.exp (a + v * s))) t)
    rw [mfderiv_comp t ((hq j).1.mdifferentiable (by simp) _) (ha.mdifferentiable (by simp) t)]
    exact ((hq j).2.2 _).comp (hai t)
  by_cases heq : removedParent 0 = removedParent 1
  · obtain ⟨a, v, ends, eta, heta, hetalt, ha, hdis, hcover0, hcross⟩ :=
      exists_source_circle_pair_complement (q (removedParent 0)) (hq _).1.continuous (hq _).2.1
        gamma hgamma hgdisjoint (fun i => by
          fin_cases i
          · exact hparent 0
          · exact heq.symm ▸ hparent 1) p hend
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (removedParent 0) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    let G := range (gamma 0) ∪ range (gamma 1)
    let U := gamma 0 '' Ioo (0 : unitInterval) 1 ∪ gamma 1 '' Ioo (0 : unitInterval) 1
    have hparC : range (q (removedParent 0)) ∩ C = G := by
      ext y
      constructor
      · rintro ⟨hy, hc⟩
        obtain ⟨i, hi⟩ := (hmemC y (hqSigma _ hy)).mp hc
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
      · rintro (hy | hy)
        · exact ⟨hparent 0 hy, hgC 0 hy⟩
        · exact ⟨heq.symm ▸ hparent 1 hy, hgC 1 hy⟩
    have hparV : range (q (removedParent 0)) ∩ V = U := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        obtain ⟨i, hi⟩ := (hmemV y (hqSigma _ hy)).mp hv
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
      · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact ⟨hparent 0 ⟨t, rfl⟩, hgV 0 ⟨t, ht, rfl⟩⟩
        · exact ⟨heq.symm ▸ hparent 1 ⟨t, rfl⟩, hgV 1 ⟨t, ht, rfl⟩⟩
    have hAR (k : Fin 2) : range (alpha k) ⊆ range (q (removedParent 0)) := by
      rintro y ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    have hcover : Sigma \ V = (⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1) ∪
        (⋃ j ∈ bypass, range (q j)) := by
      ext y
      constructor
      · rintro ⟨hyS, hyV⟩
        obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
        by_cases hj0 : j = removedParent 0
        · subst j
          apply Or.inl
          rw [← hcover0]
          refine ⟨hj, ?_⟩
          intro hyU
          have hh : y ∈ range (q (removedParent 0)) ∩ V := by rwa [hparV]
          exact hyV hh.2
        · apply Or.inr
          exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨(hbmem j).mpr
            ⟨hj0, fun hj1 => hj0 (hj1.trans heq.symm)⟩, hj⟩⟩
      · rintro (hy | hy)
        · rw [← hcover0] at hy
          refine ⟨hqSigma _ hy.1, ?_⟩
          intro hv
          apply hy.2
          change y ∈ U
          rw [← hparV]
          exact ⟨hy.1, hv⟩
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
          obtain ⟨hj, hy⟩ := mem_iUnion.mp hj
          exact hbext j hj hy
    refine ⟨removedParent, fun _ => removedParent 0, a, v, ends, eta,
      hpi, heta, hetalt, hparent, ?_, hdis, ?_, hbiff, hcover, hboundary, hcard, ?_, ?_⟩
    · intro k
      obtain ⟨hv, hvpi, hai, h0, h1, had, hac, ht0, ht1⟩ := ha k
      have hs := hsmooth (removedParent 0) (a k) (v k) (abs_pos.mp hv)
      have hd : Disjoint (alpha k '' Ioo (0 : ℝ) 1) C := by
        apply Set.disjoint_left.mpr
        rintro y ⟨t, ht, rfl⟩ hyC
        apply Set.disjoint_left.mp had ⟨t, ht, rfl⟩
        change alpha k t ∈ G
        rw [← hparC]
        exact ⟨hAR k ⟨t, rfl⟩, hyC⟩
      have hinc : alpha k '' Icc (0 : ℝ) 1 ⊆ range (q (removedParent 0)) :=
        (image_subset_range _ _).trans (hAR k)
      change (alpha k '' Icc (0 : ℝ) 1) ∩ G = {p (ends (k, 0)), p (ends (k, 1))} at hac
      rw [← hparC, ← inter_assoc, inter_eq_left.mpr hinc] at hac
      refine ⟨hv, hvpi, hs.1, hs.2, hai, h0, h1, hd, hac, ?_, ?_⟩
      · intro t ht
        rcases ht0 t ht with hh | hh
        · exact hgV 0 hh
        · exact hgV 1 hh
      · intro t ht
        rcases ht1 t ht with hh | hh
        · exact hgV 0 hh
        · exact hgV 1 hh
    · intro k j hj
      exact (hdisjoint (removedParent 0) j (hnotparent 0 j hj)).mono
        ((image_subset_range _ _).trans (hAR k)) Subset.rfl
    · intro hn
      exact False.elim (hn heq)
    · intro _
      exact ⟨fun _ => rfl, hcross⟩
  · have hrinj : Injective removedParent := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact False.elim (heq hij) | exact False.elim (heq hij.symm)
    have honly (i j : Fin 2) (y : UnitTwoSphere)
        (hi : y ∈ range (q (removedParent i))) (hj : y ∈ range (gamma j)) : j = i := by
      by_contra hji
      exact Set.disjoint_left.mp (hdisjoint (removedParent i) (removedParent j)
        (hrinj.ne (fun h => hji h.symm)))
        hi (hparent j hj)
    have hparC (i : Fin 2) : range (q (removedParent i)) ∩ C = range (gamma i) := by
      ext y
      constructor
      · rintro ⟨hy, hc⟩
        obtain ⟨j, hj⟩ := (hmemC y (hqSigma _ hy)).mp hc
        exact (honly i j y hy hj) ▸ hj
      · intro hy
        exact ⟨hparent i hy, hgC i hy⟩
    have hparV (i : Fin 2) :
        range (q (removedParent i)) ∩ V = gamma i '' Ioo (0 : unitInterval) 1 := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        obtain ⟨j, t, ht, hty⟩ := (hmemV y (hqSigma _ hy)).mp hv
        have hji := honly i j y hy ⟨t, hty⟩
        subst j
        exact ⟨t, ht, hty⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨hparent i ⟨t, rfl⟩, hgV i ⟨t, ht, rfl⟩⟩
    choose a v eta0 hv hvpi he0 he0lt hAcont hAi h0 h1 hAo hAc ht0 ht1 using
      (fun i : Fin 2 => exists_source_circle_complement (q (removedParent i))
        (hq _).1.continuous (hq _).2.1 (gamma i) (hgamma i).1 (hgamma i).2 (hparent i))
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (removedParent k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    let eta : ℝ := min (eta0 0) (eta0 1)
    have heta : 0 < eta := lt_min (he0 0) (he0 1)
    have hetale (k : Fin 2) : eta ≤ eta0 k := by
      fin_cases k
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hetalt : eta < 1 / 8 := (hetale 0).trans_lt (he0lt 0)
    have hAR (k : Fin 2) : range (alpha k) ⊆ range (q (removedParent k)) := by
      rintro y ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    have havoid (k : Fin 2) : Disjoint (alpha k '' Ioo (0 : ℝ) 1) C := by
      apply Set.disjoint_left.mpr
      intro y hy hc
      have hh : y ∈ range (q (removedParent k)) \ range (gamma k) := by rwa [hAo k]
      apply hh.2
      rw [← hparC k]
      exact ⟨hh.1, hc⟩
    have hcoverParent (i : Fin 2) (y : UnitTwoSphere)
        (hy : y ∈ range (q (removedParent i))) (hn : y ∉ V) :
        y ∈ ⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1 := by
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [← hAc i]
      exact ⟨hy, fun hh => hn (hgV i hh)⟩
    have hcover : Sigma \ V = (⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1) ∪
        (⋃ j ∈ bypass, range (q j)) := by
      ext y
      constructor
      · rintro ⟨hyS, hyV⟩
        obtain ⟨j, hj⟩ := mem_iUnion.mp hyS
        by_cases hj0 : j = removedParent 0
        · exact Or.inl (hcoverParent 0 y (hj0 ▸ hj) hyV)
        by_cases hj1 : j = removedParent 1
        · exact Or.inl (hcoverParent 1 y (hj1 ▸ hj) hyV)
        exact Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨(hbmem j).mpr ⟨hj0, hj1⟩, hj⟩⟩)
      · rintro (hy | hy)
        · obtain ⟨k, hk⟩ := mem_iUnion.mp hy
          rw [← hAc k] at hk
          refine ⟨hqSigma _ hk.1, ?_⟩
          intro hv
          apply hk.2
          rw [← hparV k]
          exact ⟨hk.1, hv⟩
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
          obtain ⟨hj, hy⟩ := mem_iUnion.mp hj
          exact hbext j hj hy
    have hdis : Disjoint (alpha 0 '' Icc (-eta) (1 + eta)) (alpha 1 '' Icc (-eta) (1 + eta)) :=
      (hdisjoint _ _ heq).mono ((image_subset_range _ _).trans (hAR 0))
        ((image_subset_range _ _).trans (hAR 1))
    refine ⟨removedParent, removedParent, a, v, ep, eta,
      hpi, heta, hetalt, hparent, ?_, hdis, ?_, hbiff, hcover, hboundary, hcard, ?_, ?_⟩
    · intro k
      have hs := hsmooth (removedParent k) (a k) (v k) (abs_pos.mp (hv k))
      have hi : InjOn (alpha k) (Icc (-eta) (1 + eta)) := (hAi k).mono
        (show Icc (-eta) (1 + eta) ⊆ Icc (-(eta0 k)) (1 + eta0 k) from
          fun t ht => ⟨by linarith [ht.1, hetale k], by linarith [ht.2, hetale k]⟩)
      have ha0 := (h0 k).trans (hend k).1
      have ha1 := (h1 k).trans (hend k).2
      have hc : (alpha k '' Icc (0 : ℝ) 1) ∩ C = {p (ep (k, 0)), p (ep (k, 1))} := by
        rw [← ha0, ← ha1]
        ext y
        constructor
        · rintro ⟨⟨t, ht, rfl⟩, hy⟩
          by_cases ht0 : t = 0
          · exact Or.inl (congrArg (alpha k) ht0)
          by_cases ht1 : t = 1
          · exact Or.inr (congrArg (alpha k) ht1)
          exact False.elim (Set.disjoint_left.mp (havoid k)
            ⟨t, ⟨lt_of_le_of_ne ht.1 (fun h => ht0 h.symm),
              lt_of_le_of_ne ht.2 ht1⟩, rfl⟩ hy)
        · rintro (rfl | rfl)
          · exact ⟨⟨0, by norm_num, rfl⟩, (h0 k).symm ▸ hgC k ⟨0, rfl⟩⟩
          · exact ⟨⟨1, by norm_num, rfl⟩, (h1 k).symm ▸ hgC k ⟨1, rfl⟩⟩
      refine ⟨hv k, hvpi k, hs.1, hs.2, hi, ha0, ha1, havoid k, hc, ?_, ?_⟩
      · intro t ht
        exact hgV k (ht0 k t ⟨by linarith [ht.1, hetale k], ht.2⟩)
      · intro t ht
        exact hgV k (ht1 k t ⟨ht.1, by linarith [ht.2, hetale k]⟩)
    · intro k j hj
      exact (hdisjoint (removedParent k) j (hnotparent k j hj)).mono
        ((image_subset_range _ _).trans (hAR k)) Subset.rfl
    · intro _
      exact ⟨rfl, fun _ => rfl⟩
    · intro hh
      exact False.elim (heq hh)

end PoincareConjecture.M25.Topology3D
