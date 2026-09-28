import PoincareConjecture.Proofs.M76.Mathlib.StableTwoTorus











set_option autoImplicit false

open Set Geometry

namespace StableTorus







theorem exists_threeTorus_band_PL_immersion :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
    let A := prodCharts (prodCharts Q Q) Q
    let B := prodCharts (prodCharts (realCharts ℝ) Q) Q
    ∃ g : (Circle × Circle) × Circle → (ℝ × Circle) × Circle,
      IsLocalHomeomorphOn g (threeBands (1 / 16)) ∧
      PLInCharts A B g (threeBands (1 / 16)) ∧
      (∀ z ∈ threeBands (1 / 16), |(g z).1.1| ≤ 9) ∧
      ∀ r s t : ℝ, |r| ≤ 1 / 32 →
        g (((r : Circle), (s : Circle)), (t : Circle)) = ((r, (s : Circle)), (t : Circle)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
  let A := prodCharts Q Q
  let B := prodCharts (realCharts ℝ) Q
  obtain ⟨f, g, hf, hfimage, hfPL, hg, hgPL, hprod, hfbound, _, hgcore⟩ :=
    exists_stable_twoTorus
  have hQid := AddCircle.plInCharts_id (4 * (16 : ℝ))
  have hAid : PLInCharts A A id univ :=
    (hQid.prodMap hQid).mono isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hreal := plInCharts_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  have hBid : PLInCharts B B id univ :=
    (hreal.prodMap hQid).mono isOpen_univ (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hAc := prodCharts_cover Q Q (AddCircle.quotientCharts_cover _)
    (AddCircle.quotientCharts_cover _)
  have hBc := prodCharts_cover (realCharts ℝ) Q (realCharts_cover ℝ)
    (AddCircle.quotientCharts_cover _)
  obtain ⟨w, hwc, hw, hwo, hwcore, hwPL⟩ :=
    exists_threeBand_cutoff (r := (1 / 16 : ℝ)) (R := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  let W := (twoBands (1 / 4) ×ˢ (univ : Set Circle)) ∪ (univ ×ˢ arc (1 / 8))
  have hwideW : threeBands (1 / 8) ⊆ W := by
    intro z hz
    rcases hz with hx | hy
    · exact Or.inl ⟨twoBands_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4) hx.1, mem_univ _⟩
    · exact Or.inr hy
  have hcoreW : threeBands (1 / 16) ⊆ W := by
    intro z hz
    rcases hz with hx | hy
    · exact Or.inl ⟨twoBands_mono (by norm_num : (1 / 16 : ℝ) ≤ 1 / 4) hx.1, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, arc_mono (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8) hy.2⟩
  obtain ⟨_, G, _, _, _, hG, hGPL, _, hGo, _, _, hGprov⟩ :=
    StableCylinder.exists_stable_circle_step hAid hBid hAc hBc
      (4 * (16 : ℝ)) (by norm_num) (delta := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
      f g (twoBands (1 / 4)) (isOpen_twoBands (by norm_num)) hf hfimage hg hprod hfPL hgPL
      (threeBands (1 / 16)) w hwc hw (fun z hz => hwo z (fun h => hz (hwideW h))) hwcore hwPL
  refine ⟨G, hG.mono hcoreW, hGPL.mono (isOpen_threeBands (by norm_num)) hcoreW, ?_, ?_⟩
  · intro z hz
    obtain ⟨s, hs, he⟩ := hGprov z (hcoreW hz)
    rw [congrArg Prod.fst he]
    exact hfbound (z.1, s) ⟨mem_univ _, hs⟩
  · intro r s t hr
    have hr4 : r ∈ Ioo (-(1 / 4)) (1 / 4) := by
      constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2]
    have hmem : (((r : Circle), (s : Circle)), (t : Circle)) ∈ twoBands (1 / 4) ×ˢ univ :=
      ⟨Or.inl ⟨⟨r, hr4, rfl⟩, mem_univ _⟩, mem_univ _⟩
    rw [hGo hmem]
    change (g ((r : Circle), (s : Circle)), (t : Circle)) =
      ((r, (s : Circle)), (t : Circle))
    rw [hgcore r s (by linarith)]

end StableTorus
