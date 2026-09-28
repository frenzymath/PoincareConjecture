import PoincareConjecture.Proofs.M76.Mathlib.StableCircleStep
import PoincareConjecture.Proofs.M76.Mathlib.StableTorusBands
import PoincareConjecture.Proofs.M76.Mathlib.StableAnnulusImmersion

set_option autoImplicit false

open Set Geometry

namespace StableTorus

theorem exists_stable_twoTorus :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
    let A := prodCharts Q Q
    let B := prodCharts (realCharts ℝ) Q
    ∃ (f : (Circle × Circle) × ℝ → (ℝ × Circle) × ℝ)
      (g : Circle × Circle → ℝ × Circle),
      IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo f (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      PLInCharts (prodCharts A (realCharts ℝ)) (prodCharts B (realCharts ℝ))
        f (univ ×ˢ Ioo (-1) 1) ∧
      IsLocalHomeomorphOn g (twoBands (1 / 4)) ∧ PLInCharts A B g (twoBands (1 / 4)) ∧
      EqOn f (fun z => (g z.1, z.2)) (twoBands (1 / 4) ×ˢ Ioo (-1) 1) ∧
      (∀ z ∈ univ ×ˢ Ioo (-1) 1, |(f z).1.1| ≤ 9) ∧
      (∀ z ∈ twoBands (1 / 4), |(g z).1| ≤ 9) ∧
      ∀ r s : ℝ, |r| ≤ 1 / 4 → g ((r : Circle), (s : Circle)) = (r, (s : Circle)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.quotientCharts (4 * (16 : ℝ))
  let R := realCharts ℝ
  let q := AddCircle.shortArcQuotient (4 * (16 : ℝ)) 1
  let U := arc 1
  have hqS : q.source = Ioo (-1) 1 := AddCircle.shortArcQuotient_source _ (by norm_num)
  have hqT : q.target = U := AddCircle.shortArcQuotient_target _ (by norm_num)
  obtain ⟨f0, hf0, hf0image, _, hf0bound, hf0core, hf0rawPL⟩ :=
    StableAnnulus.exists_stable_circle_PL_immersion
  have hg0 : IsLocalHomeomorphOn q.symm U := by
    rw [← hqT]
    exact IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn q.symm
  have hg0PL : PLInCharts Q R q.symm U := by
    rw [← hqT]
    exact AddCircle.plInCharts_shortArc_inverse _ 1
  have hf0prod : EqOn f0 (fun z => (q.symm z.1, z.2)) (U ×ˢ Ioo (-1) 1) := by
    rintro z ⟨⟨s, hs, he⟩, ht⟩
    have hz : z = ((s : Circle), z.2) := Prod.ext he.symm rfl
    rw [hz, hf0core s (abs_lt.mpr hs).le z.2 ht]
    change (s, z.2) =
      ((AddCircle.shortArcQuotient (4 * (16 : ℝ)) 1).symm (s : Circle), z.2)
    rw [AddCircle.shortArcQuotient_symm_coe (4 * (16 : ℝ)) (by norm_num) hs]
  have hf0PL : PLInCharts (prodCharts Q R) (prodCharts R R) f0 (univ ×ˢ Ioo (-1) 1) := by
    refine ⟨isOpen_univ.prod isOpen_Ioo, hf0.continuousOn, ?_⟩
    intro i j
    have hdom : chartMapDomain (prodCharts Q R i) (prodCharts R R j)
        f0 (univ ×ˢ Ioo (-1) 1) =
        (prodCharts Q R i).source ∩ prodCharts Q R i ⁻¹' (univ ×ˢ Ioo (-1) 1) := by
      ext x
      change ((x ∈ (prodCharts Q R i).source ∧ _) ∧ (f0 (prodCharts Q R i x)).1 ∈ univ ∧
        (f0 (prodCharts Q R i x)).2 ∈ univ) ↔ _
      simp
    rw [hdom]
    exact hf0rawPL i.1
  obtain ⟨w, hwc, hw, hwo, hwcore, hwPL⟩ :=
    exists_twoBand_cutoff (r := (1 / 4 : ℝ)) (R := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  let W := (U ×ˢ (univ : Set Circle)) ∪ (univ ×ˢ arc (1 / 2))
  have hhalfW : twoBands (1 / 2) ⊆ W := by
    intro z hz
    rcases hz with hx | hy
    · exact Or.inl ⟨arc_mono (by norm_num : (1 / 2 : ℝ) ≤ 1) hx.1, mem_univ _⟩
    · exact Or.inr hy
  have hcoreW : twoBands (1 / 4) ⊆ W :=
    (twoBands_mono (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)).trans hhalfW
  have hidR : PLInCharts R R id univ :=
    plInCharts_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  obtain ⟨f, g, hf, hfimage, hfPL, hg, hgPL, hprod, hgo, _, hfprov, hgprov⟩ :=
    StableCylinder.exists_stable_circle_step (AddCircle.plInCharts_id _) hidR
      (AddCircle.quotientCharts_cover _) (realCharts_cover ℝ)
      (4 * (16 : ℝ)) (by norm_num) (delta := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      f0 q.symm U (isOpen_arc (by norm_num)) hf0 hf0image hg0 hf0prod hf0PL hg0PL
      (twoBands (1 / 4)) w hwc hw (fun z hz => hwo z (fun h => hz (hhalfW h))) hwcore hwPL
  refine ⟨f, g, hf, hfimage, hfPL, hg.mono hcoreW,
    hgPL.mono (isOpen_twoBands (by norm_num)) hcoreW, hprod, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨t, ht, he⟩ := hfprov z hz
    rw [he]
    exact hf0bound (z.1.1, t) ⟨mem_univ _, ht⟩
  · intro z hz
    obtain ⟨t, ht, he⟩ := hgprov z (hcoreW hz)
    rw [he]
    exact hf0bound (z.1, t) ⟨mem_univ _, ht⟩
  · intro r s hr
    have hr1 : r ∈ Ioo (-1) 1 := by
      constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2]
    have hmem : ((r : Circle), (s : Circle)) ∈ U ×ˢ univ :=
      ⟨⟨r, hr1, rfl⟩, mem_univ _⟩
    rw [hgo hmem]
    change ((AddCircle.shortArcQuotient (4 * (16 : ℝ)) 1).symm (r : Circle),
      (s : Circle)) = (r, (s : Circle))
    rw [AddCircle.shortArcQuotient_symm_coe (4 * (16 : ℝ)) (by norm_num) hr1]

end StableTorus
