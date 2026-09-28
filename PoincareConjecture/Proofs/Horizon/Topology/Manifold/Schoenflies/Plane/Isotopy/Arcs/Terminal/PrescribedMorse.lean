import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PrescribedRibbon
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Ribbon



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem closedSquare_subset_compact_negativeLevelRibbon_iff
    {t a ρ : Real} (ht : 0 < t) (hρ : 0 ≤ ρ) :
    closedSquare ρ ⊆
      ((fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1)) ↔ ρ ≤ a ∧ ρ ≤ Real.sqrt t := by
  constructor
  · intro hsub
    have hx : (WithLp.toLp 2 ![0, ρ] : E2) ∈ closedSquare ρ := by
      simpa [closedSquare, abs_of_nonneg hρ] using hρ
    obtain ⟨⟨s, u⟩, ⟨hs, hu⟩, heq⟩ := hsub hx
    have hsr : s = ρ := congrArg (fun x : E2 => x 1) heq
    have hρa : ρ ≤ a := hsr ▸ hs.2
    have hy : (WithLp.toLp 2 ![ρ, 0] : E2) ∈ closedSquare ρ := by
      simpa [closedSquare, abs_of_nonneg hρ] using hρ
    obtain ⟨⟨v, q⟩, ⟨hv, hq⟩, heq'⟩ := hsub hy
    have hv0 : v = 0 := congrArg (fun x : E2 => x 1) heq'
    have hvalue : (2 * q - 1) * Real.sqrt t = ρ := by
      have h := congrArg (fun x : E2 => x 0) heq'
      simpa [negativeLevelRibbon, positiveLevelRibbon, saddleCoordinateSwap, hv0] using h
    have hfactor : |2 * q - 1| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [hq.1, hq.2]
    have hbound := mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg t)
    have hρroot : ρ ≤ Real.sqrt t := by
      calc
        ρ = |(2 * q - 1) * Real.sqrt t| := by rw [hvalue, abs_of_nonneg hρ]
        _ = |2 * q - 1| * Real.sqrt t := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
        _ ≤ Real.sqrt t := by simpa using hbound
    exact ⟨hρa, hρroot⟩
  · rintro ⟨hρa, hρroot⟩ x hx
    have hx0 : |x 0| ≤ ρ := hx.1
    have hx1 : |x 1| ≤ a := hx.2.trans hρa
    let d := Real.sqrt (t + (x 1)^2)
    have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
    have hroot : Real.sqrt t ≤ d := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x 1)])
    have hratio : |x 0 / d| ≤ 1 := by
      rw [abs_div, abs_of_pos hd]
      exact (div_le_one hd).mpr (hx0.trans (hρroot.trans hroot))
    have hq : (x 0 / d + 1) / 2 ∈ Icc (0 : Real) 1 := by
      have h := abs_le.mp hratio
      constructor <;> linarith [h.1, h.2]
    refine ⟨(x 1, (x 0 / d + 1) / 2), ⟨abs_le.mp hx1, hq⟩, ?_⟩
    ext i
    fin_cases i
    · change (2 * ((x 0 / d + 1) / 2) - 1) * d = x 0
      field_simp
      ring
    · rfl




theorem exists_disk_pair_isotopy_fixing_prescribed_negative_morse_square
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (hB : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1))
    {r t w a ρ : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hw : 0 < w) (hwr : w ≤ hyperbolaRadius r t)
    (ha : 0 < a) (haw : a < w) (hρ : 0 < ρ)
    (hρa : ρ ≤ a) (hρt : ρ ≤ Real.sqrt t)
    (hstart : ∀ s ∈ Ioo (-w) w, negativeLevelArc t 1 s ∈
      (A 0 '' sphere (0 : E2) 1) ∩ (B 0 '' sphere (0 : E2) 1))
    (hfinish : ∀ s ∈ Ioo (-w) w, negativeLevelArc t 0 s ∈
      (A 1 '' sphere (0 : E2) 1) ∩ (B 1 '' sphere (0 : E2) 1))
    (hAlevel : ∀ x ∈ openSquare r,
      x ∈ frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hBlevel : ∀ x ∈ openSquare r,
      x ∈ frontier (B 0 '' closedBall 0 1) ∪ frontier (B 1 '' closedBall 0 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    ρ < r ∧ ∃ K : Set E2, IsCompact K ∧
      Disjoint K ((fun z : Real × Real =>
        negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
          (Icc (-a) a ×ˢ Icc 0 1)) ∧
      Disjoint K (closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Φ u x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧
          ((fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
            (Icc (-a) a ×ˢ Icc 0 1)) ⊆ U ∧
          closedSquare ρ ⊆ U ∧ ∀ u, EqOn (Φ u) id U := by
  have havoid (s : Real) (hs : s ∈ Ioo (-w) w) :
      Disjoint ((fun u : Real => negativeLevelRibbonDiffeomorph ht
        (WithLp.toLp 2 ![s, u])) '' Ioo 0 1)
        ((frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1)) ∪
          (frontier (B 0 '' closedBall 0 1) ∪ frontier (B 1 '' closedBall 0 1))) := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ hx
    have hs' : s ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
      ⟨(neg_le_neg hwr).trans_lt hs.1, hs.2.trans_le hwr⟩
    have hsq := negativeLevelRibbon_mem_openSquare hr ht htr
      (z := WithLp.toLp 2 ![s, u]) (by simpa using hs')
      (by simpa using Ioo_subset_Icc_self hu)
    have hheight := negativeLevelRibbon_height_gt ht
      (z := WithLp.toLp 2 ![s, u]) (by simpa using hu)
    have heq : -(negativeLevelRibbon t (WithLp.toLp 2 ![s, u]) 0)^2 +
        (negativeLevelRibbon t (WithLp.toLp 2 ![s, u]) 1)^2 = -t := by
      rcases hx with hx | hx
      · exact hAlevel _ hsq hx
      · exact hBlevel _ hsq hx
    exact (ne_of_gt hheight) heq
  have hedge (i : Fin 2) (s : Real) (hs : s ∈ Ioo (-w) w) :
      negativeLevelRibbonDiffeomorph ht (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1) := by
    fin_cases i
    · simpa using hstart s hs
    · simpa using hfinish s hs
  obtain ⟨K, hK, hKP, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦmatch, U, hU, hPU, hΦU⟩ :=
    exists_disk_pair_isotopy_fixing_prescribed_compact_shared_ribbon
      A B hA hB (negativeLevelRibbonDiffeomorph ht) hw ha haw hedge havoid
  have hsqP := (closedSquare_subset_compact_negativeLevelRibbon_iff ht hρ.le).mpr ⟨hρa, hρt⟩
  have hρr : ρ < r := hρa.trans_lt (haw.trans_le hwr |>.trans (hyperbolaRadius_lt hr ht htr))
  exact ⟨hρr, K, hK, hKP, hKP.mono_right hsqP, Φ, hΦ0, hΦs, hΦi, hΦfix,
    hΦmatch, U, hU, hPU, hsqP.trans hPU, hΦU⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
