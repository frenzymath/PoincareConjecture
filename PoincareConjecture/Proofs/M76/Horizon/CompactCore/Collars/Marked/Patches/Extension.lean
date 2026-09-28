import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.HalfPatch

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)

theorem exists_partial_half_arm_patch_extension {a b w : ℝ}
    (ha : -(1 / 2 : ℝ) < a) (hab : a < b) (hb : b < 3 / 2)
    (hw : 0 < w) (hwsmall : w < 1 / 2)
    {g : P2 → P2} (hg : FinitePiecewiseAffineOn g (Icc a b ×ˢ Icc 0 w))
    (hgi : InjOn g (Icc a b ×ˢ Icc 0 w))
    (hmap : MapsTo g (Icc a b ×ˢ Icc 0 w)
      (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ico (0 : ℝ) (1 / 2)))
    (hcenter : ∀ t ∈ Icc a b, g (t, 0) = (t, 0))
    (hzero : ∀ p ∈ Icc a b ×ˢ Icc 0 w, (g p).2 = 0 ↔ p.2 = 0) :
    ∃ H : halfArmRectangle ≃ₜ halfArmRectangle, H.IsFinitePL ∧
      (∀ p (hp : p ∈ Icc a b ×ˢ Icc 0 w), (H ⟨p, by
        exact ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩,
          hp.2.1, hp.2.2.trans hwsmall.le⟩⟩ : P2) = g p) ∧
      ∀ p : halfArmRectangle, (p : P2) ∈ frontier halfArmRectangle → H p = p := by
  let d : Set P2 := Icc a b ×ˢ Icc 0 w
  let u : Set P2 := Icc a b ×ˢ {(0 : ℝ)}
  have rectangle_ball {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
      IsFinitePLBallPair P2 (Icc a b ×ˢ Icc c d) (frontier (Icc a b ×ˢ Icc c d)) := by
    have h := (isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc hcd)
    rwa [← h.frontier_eq_of_finrank_eq rfl] at h
  have hs : IsFinitePLBallPair P2 halfArmRectangle (frontier halfArmRectangle) :=
    rectangle_ball (by norm_num) (by norm_num)
  have hd : IsFinitePLBallPair P2 d (frontier d) := rectangle_ball hab hw
  have hds : d ⊆ halfArmRectangle := fun p hp =>
    ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩, hp.2.1, hp.2.2.trans hwsmall.le⟩
  have hu : IsFinitePLBallPair ℝ u {(a, 0), (b, 0)} := by
    let A : ℝ →ᴬ[ℝ] P2 :=
      (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
    have hA : InjOn A (Icc a b) := fun _ _ _ _ h => congrArg Prod.fst h
    have himage : A '' Icc a b = u := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ⟨ht, rfl⟩
      · rintro ⟨hx, hz⟩; exact ⟨x.1, hx, Prod.ext rfl hz.symm⟩
    have h := isFinitePLBallPair_affine_interval hab A hA
    rw [himage] at h
    exact h
  have hub : u ⊆ frontier d := by
    intro p hp
    change p ∈ frontier (Icc a b ×ˢ Icc (0 : ℝ) w)
    rw [frontier_rectangle_eq_four_sides hab.le hw.le]
    exact Or.inl (Or.inl hp)
  have huq : u ⊆ frontier halfArmRectangle := by
    intro p hp
    rw [halfArmRectangle, frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
    exact Or.inl (Or.inl ⟨⟨ha.le.trans hp.1.1, hp.1.2.trans hb.le⟩, hp.2⟩)
  have hcontact (p : P2) (hp : p ∈ d) : p ∈ frontier halfArmRectangle ↔ p ∈ u := by
    constructor
    · intro h
      rw [halfArmRectangle, frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)] at h
      rcases h with (h | h) | (h | h)
      · exact ⟨hp.1, h.2⟩
      · have he : p.2 = 1 / 2 := h.2
        exfalso; linarith [hp.2.2]
      · have he : p.1 = -(1 / 2 : ℝ) := h.1
        exfalso; linarith [hp.1.1]
      · have he : p.1 = 3 / 2 := h.1
        exfalso; linarith [hp.1.2]
    · exact fun h => huq h
  have hgcontact (p : P2) (hp : p ∈ d) : g p ∈ frontier halfArmRectangle ↔ p ∈ u := by
    have hm := hmap hp
    have hz : (g p).2 = 0 ↔ p ∈ u := (hzero p hp).trans
      ⟨fun h => ⟨hp.1, h⟩, fun h => h.2⟩
    constructor
    · intro h
      rw [halfArmRectangle, frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)] at h
      apply hz.mp
      rcases h with (h | h) | (h | h)
      · exact h.2
      · have he : (g p).2 = 1 / 2 := h.2
        exfalso; linarith [hm.2.2]
      · have he : (g p).1 = -(1 / 2 : ℝ) := h.1
        exfalso; linarith [hm.1.1]
      · have he : (g p).1 = 3 / 2 := h.1
        exfalso; linarith [hm.1.2]
    · intro h
      rw [halfArmRectangle, frontier_rectangle_eq_four_sides (by norm_num) (by norm_num)]
      exact Or.inl (Or.inl ⟨Ioo_subset_Icc_self hm.1, hz.mpr h⟩)
  obtain ⟨H, hH, hpatch, hfixed, _⟩ := exists_attached_patch_extension hs hd hds hu hub huq
    (fun h => hab.ne (congrArg Prod.fst h)) hcontact hg hgi
    (fun p hp => ⟨Ioo_subset_Icc_self (hmap hp).1, Ico_subset_Icc_self (hmap hp).2⟩)
    (fun p hp => by
      have heq : p = (p.1, 0) := Prod.ext rfl hp.2
      exact (congrArg g heq).trans ((hcenter p.1 hp.1).trans heq.symm)) hgcontact
  exact ⟨H, hH, fun p hp => hpatch ⟨p, hp⟩, hfixed⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
