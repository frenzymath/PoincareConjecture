import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.CompleteExcursionFamily



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

def annularLiftAboveAxis (r : ℝ → P2) (c : ℝ) (t : ℝ) : P2 :=
  ((r t).2, (r t).1 - c)

def annularUpperHalfStrip : Set P2 := Icc (-1 : ℝ) 1 ×ˢ Ici (0 : ℝ)

theorem mem_frontier_annularUpperHalfStrip {z : P2} (hz : z ∈ annularUpperHalfStrip) :
    z ∈ frontier annularUpperHalfStrip ↔ z.1 = -1 ∨ z.1 = 1 ∨ z.2 = 0 := by
  have hclosed : IsClosed annularUpperHalfStrip := isClosed_Icc.prod isClosed_Ici
  rw [frontier, hclosed.closure_eq, mem_sdiff, and_iff_right hz]
  rw [annularUpperHalfStrip, interior_prod_eq, interior_Icc, interior_Ici]
  change ¬ ((-1 < z.1 ∧ z.1 < 1) ∧ 0 < z.2) ↔ _
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    exact ⟨⟨lt_of_le_of_ne hz.1.1 (Ne.symm hn.1), lt_of_le_of_ne hz.1.2 hn.2.1⟩,
      lt_of_le_of_ne hz.2 (Ne.symm hn.2.2)⟩
  · intro h hh
    rcases h with h | h | h <;> linarith [hh.1.1, hh.1.2, hh.2]

theorem exists_complete_upper_arc_family {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1)
    {c : ℝ} (h0 : (r 0).1 ≠ c) (h1 : (r 1).1 ≠ c)
    (hfinite : {t ∈ Icc (0 : ℝ) 1 | (r t).1 = c}.Finite)
    (hreg : ∀ x ∈ Icc (0 : ℝ) 1, (r x).1 = c →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (r y).1 - c = m * (y - x)) :
    ∃ J : Finset (ℝ × ℝ),
      (∀ p ∈ J, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
        IsFinitePLBallPair ℝ (annularLiftAboveAxis r c '' Icc p.1 p.2)
          {annularLiftAboveAxis r c p.1, annularLiftAboveAxis r c p.2} ∧
        annularLiftAboveAxis r c p.1 ≠ annularLiftAboveAxis r c p.2 ∧
        annularLiftAboveAxis r c '' Icc p.1 p.2 ⊆ annularUpperHalfStrip ∧
        (annularLiftAboveAxis r c '' Icc p.1 p.2) ∩ frontier annularUpperHalfStrip =
          {annularLiftAboveAxis r c p.1, annularLiftAboveAxis r c p.2}) ∧
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        Disjoint (annularLiftAboveAxis r c '' Icc p.1 p.2)
          (annularLiftAboveAxis r c '' Icc q.1 q.2)) ∧
      (annularLiftAboveAxis r c '' Icc (0 : ℝ) 1) ∩ annularUpperHalfStrip =
        ⋃ p ∈ J, annularLiftAboveAxis r c '' Icc p.1 p.2 := by
  let f : ℝ → ℝ := fun t => (r t).1
  have hf : FinitePiecewiseAffineOn f (Icc 0 1) :=
    hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  obtain ⟨J, hJ, hdis, hcover⟩ :=
    exists_complete_positive_interval_family hf h0 h1 hfinite hreg
  let A : P2 →ᴬ[ℝ] P2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap - ContinuousAffineMap.const ℝ P2 c)
  have hq : FinitePiecewiseAffineOn (annularLiftAboveAxis r c) (Icc 0 1) := hr.postcomp A
  have hqi : InjOn (annularLiftAboveAxis r c) (Icc 0 1) := by
    intro s hs t ht h
    apply hi hs ht
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    apply Prod.ext
    · change (r s).1 - c = (r t).1 - c at hsnd
      linarith
    · exact hfst
  have hsub (p : P2) (hp : p ∈ J) : Icc p.1 p.2 ⊆ Icc (0 : ℝ) 1 := by
    obtain ⟨ha, _, hb, _⟩ := hJ p hp
    exact fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hmem (p : P2) (hp : p ∈ J) (t : ℝ) (ht : t ∈ Icc p.1 p.2) :
      annularLiftAboveAxis r c t ∈ annularUpperHalfStrip := by
    have hlevel : c ≤ f t := (hcover.symm.subset (mem_iUnion₂.mpr ⟨p, hp, ht⟩)).2
    exact ⟨hheight t (hsub p hp ht), sub_nonneg.mpr hlevel⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨ha, hab, hb, hfa, hfb, _, _, hpos⟩ := hJ p hp
    have hball : IsFinitePLBallPair ℝ (annularLiftAboveAxis r c '' Icc p.1 p.2)
        {annularLiftAboveAxis r c p.1, annularLiftAboveAxis r c p.2} := by
      simpa only [image_pair] using
        (isFinitePLBallPair_Icc hab).image_of_subset hq (hsub p hp) hqi
    have hend {t : ℝ} (ht : t = p.1 ∨ t = p.2) :
        annularLiftAboveAxis r c t ∈ frontier annularUpperHalfStrip := by
      rcases ht with rfl | rfl
      · rw [mem_frontier_annularUpperHalfStrip (hmem p hp _ ⟨le_rfl, hab.le⟩)]
        rcases hfa with h | h
        · exact Or.inl (by change (r p.1).2 = -1; rw [h, hbottom])
        · exact Or.inr (Or.inr (sub_eq_zero.mpr h))
      · rw [mem_frontier_annularUpperHalfStrip (hmem p hp _ ⟨hab.le, le_rfl⟩)]
        rcases hfb with h | h
        · exact Or.inr (Or.inl (by change (r p.2).2 = 1; rw [h, htop]))
        · exact Or.inr (Or.inr (sub_eq_zero.mpr h))
    refine ⟨ha, hab, hb, hball,
      (fun h => hab.ne (hqi (hsub p hp ⟨le_rfl, hab.le⟩)
        (hsub p hp ⟨hab.le, le_rfl⟩) h)),
      (by rintro _ ⟨t, ht, rfl⟩; exact hmem p hp t ht), ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, htfront⟩
      by_cases hta : t = p.1
      · simp [hta]
      by_cases htb : t = p.2
      · simp [htb]
      have hti : t ∈ Ioo p.1 p.2 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
      have hH := hproper t ⟨ha.trans_lt hti.1, hti.2.trans_le hb⟩
      have hP := hpos t hti
      rcases (mem_frontier_annularUpperHalfStrip (hmem p hp t ht)).mp htfront with h | h | h
      · exact (hH.1.ne' h).elim
      · exact (hH.2.ne h).elim
      · change (r t).1 - c = 0 at h
        exact (not_lt_of_ge (by dsimp [f]; linarith) hP).elim
    · rintro _ (rfl | rfl)
      · exact ⟨mem_image_of_mem _ ⟨le_rfl, hab.le⟩, hend (Or.inl rfl)⟩
      · exact ⟨mem_image_of_mem _ ⟨hab.le, le_rfl⟩, hend (Or.inr rfl)⟩
  · intro p hp q hq hpq
    apply disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
    have heq := hqi (hsub q hq ht) (hsub p hp hs) hts
    exact disjoint_left.mp (hdis p hp q hq hpq) hs (heq ▸ ht)
  · apply Subset.antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, htD⟩
      have hlevel : c ≤ f t := by
        have hh := htD.2
        change 0 ≤ (r t).1 - c at hh
        dsimp [f]; linarith
      obtain ⟨p, hp, htp⟩ := mem_iUnion₂.mp (hcover.subset ⟨ht, hlevel⟩)
      exact mem_iUnion₂.mpr ⟨p, hp, mem_image_of_mem _ htp⟩
    · intro z hz
      obtain ⟨p, hp, t, ht, rfl⟩ := mem_iUnion₂.mp hz
      exact ⟨mem_image_of_mem _ (hsub p hp ht), hmem p hp t ht⟩

end PoincareConjecture.M76.Dehn
