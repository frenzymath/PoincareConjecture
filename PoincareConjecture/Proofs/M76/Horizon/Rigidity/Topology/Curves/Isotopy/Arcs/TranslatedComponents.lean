import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.UpperComponents

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem finite_annular_translates_meeting_strip {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (c d : ℝ) :
    {k : ℤ | ∃ t ∈ Icc (0 : ℝ) 1,
      (r t).1 - (c + 32 * (k : ℝ)) ∈ Icc 0 d}.Finite := by
  have hc := isCompact_Icc.image_of_continuousOn
    (continuous_fst.comp_continuousOn hr.continuousOn)
  obtain ⟨lo, hlo⟩ := hc.bddBelow
  obtain ⟨hi, hhi⟩ := hc.bddAbove
  apply (finite_Icc (⌊(lo - c - d) / 32⌋ : ℤ) (⌈(hi - c) / 32⌉ : ℤ)).subset
  rintro k ⟨t, ht, htk⟩
  have hl := hlo (mem_image_of_mem (fun t => (r t).1) ht)
  have hu := hhi (mem_image_of_mem (fun t => (r t).1) ht)
  have hfl := Int.floor_le ((lo - c - d) / 32)
  have hce := Int.le_ceil ((hi - c) / 32)
  constructor
  · have : ((⌊(lo - c - d) / 32⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by linarith [htk.2]
    exact_mod_cast this
  · have : (k : ℝ) ≤ ((⌈(hi - c) / 32⌉ : ℤ) : ℝ) := by linarith [htk.1]
    exact_mod_cast this

theorem annular_translated_upper_images_disjoint {r : ℝ → P2}
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    (c : ℝ) {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc (0 : ℝ) 1)
      (annularLiftAboveAxis r (c + 32 * (l : ℝ)) '' Icc (0 : ℝ) 1) := by
  apply disjoint_left.mpr
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
  have hh := congrArg Prod.fst hts
  have ha := congrArg Prod.snd hts
  have he : r s = r t + (32 * ((k - l : ℤ) : ℝ), 0) := by
    apply Prod.ext
    · change (r s).1 = (r t).1 + 32 * ((k - l : ℤ) : ℝ)
      change (r t).1 - (c + 32 * (l : ℝ)) = (r s).1 - (c + 32 * (k : ℝ)) at ha
      rw [Int.cast_sub]
      linarith
    · simpa only [annularLiftAboveAxis, Prod.snd_add, add_zero] using hh.symm
  exact hkl (sub_eq_zero.mp (htranslate s t hs ht (k - l) he).2)

theorem exists_generic_complete_upper_arc_families {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1) :
    ∃ c ∈ Ioo (0 : ℝ) 32, ∃ J : ℤ → Finset (ℝ × ℝ),
      (∀ k p, p ∈ J k → 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
        IsFinitePLBallPair ℝ (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc p.1 p.2)
          {annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.1,
            annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.2} ∧
        annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.1 ≠
          annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.2 ∧
        annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc p.1 p.2 ⊆ annularUpperHalfStrip ∧
        (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc p.1 p.2) ∩
          frontier annularUpperHalfStrip =
          {annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.1,
            annularLiftAboveAxis r (c + 32 * (k : ℝ)) p.2}) ∧
      (∀ k p, p ∈ J k → ∀ q ∈ J k, p ≠ q →
        Disjoint (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc p.1 p.2)
          (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc q.1 q.2)) ∧
      ∀ k : ℤ, (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc (0 : ℝ) 1) ∩
        annularUpperHalfStrip =
          ⋃ p ∈ J k, annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc p.1 p.2 := by
  have hf : FinitePiecewiseAffineOn (fun t => (r t).1) (Icc 0 1) :=
    hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  obtain ⟨c, hc, hfinite, hreg⟩ := exists_generic_annular_axis hf
  have hfinite' (k : ℤ) : {t ∈ Icc (0 : ℝ) 1 | (r t).1 = c + 32 * (k : ℝ)}.Finite :=
    hfinite.subset (fun _ hx => ⟨hx.1, k, hx.2⟩)
  have hreg' (k : ℤ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
      (hfx : (r x).1 = c + 32 * (k : ℝ)) :
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x) := by
    obtain ⟨u, v, m, _, hux, hxv, _, hm, hformula⟩ := hreg x k hx hfx
    exact ⟨u, v, m, hux, hxv, hm, hformula⟩
  have hend0 (k : ℤ) : (r 0).1 ≠ c + 32 * (k : ℝ) := by
    intro h
    obtain ⟨u, v, m, hu, hux, _⟩ := hreg 0 k ⟨le_rfl, zero_le_one⟩ h
    linarith
  have hend1 (k : ℤ) : (r 1).1 ≠ c + 32 * (k : ℝ) := by
    intro h
    obtain ⟨u, v, m, _, _, hxv, hv, _⟩ := hreg 1 k ⟨zero_le_one, le_rfl⟩ h
    linarith
  choose J hJ hdis hcover using fun k => exists_complete_upper_arc_family hr hi
    hheight hproper hbottom htop (hend0 k) (hend1 k) (hfinite' k) (hreg' k)
  exact ⟨c, hc, J, hJ, hdis, hcover⟩

end PoincareConjecture.M76.Dehn
