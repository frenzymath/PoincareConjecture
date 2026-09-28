import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Patches.Signed
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.Pasting



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)

theorem exists_rimCylinder_correction_of_partial_patches
    (a b w : Bool → ℝ) (ha : ∀ i, -(1 / 2 : ℝ) < a i)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i < 3 / 2)
    (hw : ∀ i, 0 < w i) (hwsmall : ∀ i, w i ≤ 1 / 2)
    (g : Bool → P2 → P2)
    (hg : ∀ i, FinitePiecewiseAffineOn (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i)))
    (hi : ∀ i, InjOn (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i)))
    (hmap : ∀ i, MapsTo (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i))
      (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hcenter : ∀ i t, t ∈ Icc (a i) (b i) → g i (0, t) = (t, 0))
    (hzero : ∀ i p, p ∈ Icc (-w i) (w i) ×ˢ Icc (a i) (b i) →
      ((g i p).2 = 0 ↔ p.1 = 0)) :
    ∃ (o : Bool → Bool) (G : rimCylinder ≃ₜ rimCylinder), G.IsFinitePL ∧
      (∀ x : rimCylinder, (x : V2 × ℝ).2 = 0 ∨ (x : V2 × ℝ).2 = -(1 / 2 : ℝ) ∨
        (x : V2 × ℝ).2 = 1 / 2 → G x = x) ∧
      ∀ i side p (hp : p ∈ Icc (a i) (b i) ×ˢ Icc 0 (w i / 2)),
        (G ⟨halfArmChart (i, side) p, halfArmCarrier_cover ▸ mem_iUnion.mpr
          ⟨(i, side), p, ⟨⟨(ha i).le.trans hp.1.1, hp.1.2.trans (hb i).le⟩,
            hp.2.1, by linarith [hp.2.2, hwsmall i]⟩, rfl⟩⟩ : V2 × ℝ) =
          (armPoint i (g i (sign (o i) * (sign side * p.2), p.1)).1,
            (g i (sign (o i) * (sign side * p.2), p.1)).2) := by
  classical
  choose o H hH hfixed hvalue using fun i => exists_partial_signed_patches
    (ha i) (hab i) (hb i) (hw i) (hwsmall i) (hg i) (hi i) (hmap i) (hcenter i) (hzero i)
  obtain ⟨G, hG, hchart, hkeep⟩ := exists_rimCylinder_homeomorph
    (fun i => H i.1 i.2) (fun i => hH i.1 i.2) (fun i => hfixed i.1 i.2)
  refine ⟨o, G, hG, hkeep, ?_⟩
  intro i side p hp
  have hpR : p ∈ halfArmRectangle :=
    ⟨⟨(ha i).le.trans hp.1.1, hp.1.2.trans (hb i).le⟩,
      hp.2.1, by linarith [hp.2.2, hwsmall i]⟩
  have h := hchart (i, side) ⟨p, hpR⟩
  change (G _ : V2 × ℝ) = halfArmChart (i, side) (H i side ⟨p, hpR⟩) at h
  rw [show halfArmChart (i, side) (H i side ⟨p, hpR⟩) =
      (armPoint i (g i (sign (o i) * (sign side * p.2), p.1)).1,
        (g i (sign (o i) * (sign side * p.2), p.1)).2) from ?_] at h
  · exact h
  · rw [hvalue i side p hp]
    cases side <;> simp [halfArmChart, sign]


theorem exists_rimCylinder_correction_with_signed_formula
    (a b w : Bool → ℝ) (ha : ∀ i, -(1 / 2 : ℝ) < a i)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i < 3 / 2)
    (hw : ∀ i, 0 < w i) (hwsmall : ∀ i, w i ≤ 1 / 2)
    (g : Bool → P2 → P2)
    (hg : ∀ i, FinitePiecewiseAffineOn (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i)))
    (hi : ∀ i, InjOn (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i)))
    (hmap : ∀ i, MapsTo (g i) (Icc (-w i) (w i) ×ˢ Icc (a i) (b i))
      (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hcenter : ∀ i t, t ∈ Icc (a i) (b i) → g i (0, t) = (t, 0))
    (hzero : ∀ i p, p ∈ Icc (-w i) (w i) ×ˢ Icc (a i) (b i) →
      ((g i p).2 = 0 ↔ p.1 = 0)) :
    ∃ (o : Bool → Bool) (G : rimCylinder ≃ₜ rimCylinder), G.IsFinitePL ∧
      (∀ x : rimCylinder, (x : V2 × ℝ).2 = 0 ∨ (x : V2 × ℝ).2 = -(1 / 2 : ℝ) ∨
        (x : V2 × ℝ).2 = 1 / 2 → G x = x) ∧
      ∀ i s t (x : rimCylinder), s ∈ Icc (a i) (b i) → |t| ≤ w i / 2 →
        (x : V2 × ℝ) = (armPoint i s, t) →
        (G x : V2 × ℝ) = (armPoint i (g i (sign (o i) * t, s)).1,
          (g i (sign (o i) * t, s)).2) := by
  obtain ⟨o, G, hG, hfixed, hformula⟩ :=
    exists_rimCylinder_correction_of_partial_patches a b w ha hab hb hw hwsmall
      g hg hi hmap hcenter hzero
  refine ⟨o, G, hG, hfixed, ?_⟩
  intro i s t x hs ht hx
  obtain ⟨side, u, hu, htu⟩ : ∃ (side : Bool) (u : ℝ), 0 ≤ u ∧ u ≤ w i / 2 ∧
      sign side * u = t := by
    by_cases ht0 : 0 ≤ t
    · exact ⟨false, t, ht0, by simpa [abs_of_nonneg ht0] using ht, by simp [sign]⟩
    · refine ⟨true, -t, by linarith, ?_, ?_⟩
      · simpa [abs_of_neg (lt_of_not_ge ht0)] using ht
      · simp [sign]
  have hvalue := hformula i side (s, u) ⟨hs, hu, htu.1⟩
  have heq : halfArmChart (i, side) (s, u) = (x : V2 × ℝ) := by
    rw [hx]
    exact Prod.ext rfl htu.2
  have hsource (hmem : halfArmChart (i, side) (s, u) ∈ rimCylinder) :
      (⟨halfArmChart (i, side) (s, u), hmem⟩ : rimCylinder) = x := Subtype.ext heq
  rw [hsource] at hvalue
  simpa only [htu.2] using hvalue

end PoincareConjecture.M76.Dehn.Annuli.RimBands
