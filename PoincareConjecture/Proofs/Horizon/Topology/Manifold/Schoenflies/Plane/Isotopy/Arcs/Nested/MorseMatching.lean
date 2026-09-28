import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.MorseSides



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def horizontalScale (a : Real) (ha : a ≠ 0) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![a * x 0, x 1]
  invFun x := WithLp.toLp 2 ![x 0 / a, x 1]
  left_inv x := by ext i; fin_cases i <;> simp [ha]
  right_inv x := by
    ext i
    fin_cases i
    · change a * (x 0 / a) = x 0
      field_simp
    · rfl
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.mul (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.div_const a
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff





theorem exists_supported_nested_negative_morse_isotopy
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1)
    (hB : B 1 '' closedBall 0 1 ⊆ B 0 '' ball 0 1)
    {r t a w : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (ha : 0 < a) (haw : a < w) (hwr : w ≤ hyperbolaRadius r t)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      negativeLevelRibbon t (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (hAlevel : ∀ x ∈ openSquare r,
      x ∈ (A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t)
    (hBlevel : ∀ x ∈ openSquare r,
      x ∈ (B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1) →
      -(x 0)^2 + (x 1)^2 = -t) :
    let P := (fun z : Real × Real =>
      negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1)
    ∃ K : Set E2, IsCompact K ∧ Disjoint K P ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ u x, x ∉ K → Phi u x = x) ∧
        (∀ i, Phi 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        (∀ i, Phi 1 '' (A i '' sphere 0 1) = B i '' sphere 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧ P ⊆ U ∧ ∀ u, EqOn (Phi u) id U := by
  let R := (horizontalScale a ha.ne').trans (negativeLevelRibbonDiffeomorph ht)
  have hR (s u : Real) : R (WithLp.toLp 2 ![s, u]) =
      negativeLevelRibbon t (WithLp.toLp 2 ![a * s, u]) := rfl
  have hinterval (s : Real) (hs : s ∈ Ioo (-(w / a)) (w / a)) :
      a * s ∈ Ioo (-w) w := by
    constructor
    · have h := (div_lt_iff₀ ha).mp (show -w / a < s by simpa only [neg_div] using hs.1)
      nlinarith
    · have h := (lt_div_iff₀ ha).mp hs.2
      nlinarith
  have hedgeR (i : Fin 2) (s : Real) (hs : s ∈ Ioo (-(w / a)) (w / a)) :
      R (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1) := by
    rw [hR]
    exact hedge i _ (hinterval s hs)
  have havoid (s : Real) (hs : s ∈ Ioo (-(w / a)) (w / a)) :
      Disjoint ((fun u : Real => R (WithLp.toLp 2 ![s, u])) '' Ioo 0 1)
        (((A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1)) ∪
          ((B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1))) := by
    apply disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ hx
    dsimp only at hx
    rw [hR] at hx
    have hs' := hinterval s hs
    have hsrad : a * s ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
      ⟨(neg_le_neg hwr).trans_lt hs'.1, hs'.2.trans_le hwr⟩
    have hsq := negativeLevelRibbon_mem_openSquare hr ht htr
      (z := WithLp.toLp 2 ![a * s, u]) (by simpa using hsrad)
      (by simpa using Ioo_subset_Icc_self hu)
    have hheight := negativeLevelRibbon_height_gt ht
      (z := WithLp.toLp 2 ![a * s, u]) (by simpa using hu)
    have heq : -(negativeLevelRibbon t (WithLp.toLp 2 ![a * s, u]) 0)^2 +
        (negativeLevelRibbon t (WithLp.toLp 2 ![a * s, u]) 1)^2 = -t := by
      rcases hx with hx | hx
      · exact hAlevel _ hsq hx
      · exact hBlevel _ hsq hx
    exact (ne_of_gt hheight) heq
  have himage : (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-1) 1 ×ˢ Icc 0 1) =
      (fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1) := by
    ext y
    constructor
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      exact ⟨(a * s, u), ⟨⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, hu⟩,
        (hR s u).symm⟩
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      refine ⟨(s / a, u), ⟨⟨?_, ?_⟩, hu⟩, ?_⟩
      · apply (le_div_iff₀ ha).mpr
        linarith [hs.1]
      · apply (div_le_iff₀ ha).mpr
        linarith [hs.2]
      · change R (WithLp.toLp 2 ![s / a, u]) =
          negativeLevelRibbon t (WithLp.toLp 2 ![s, u])
        rw [hR]
        congr 2
        field_simp
  obtain ⟨K, hK, hKP, Phi, hPhi0, hPhis, hPhii, hPhifix, hmatch, U, hU, hPU, hfixU⟩ :=
    exists_supported_nested_disk_pair_isotopy_of_shared_ribbon A B hA hB R
      ((one_lt_div ha).mpr haw) hedgeR havoid
  refine ⟨K, hK, himage ▸ hKP, Phi, hPhi0, hPhis, hPhii, hPhifix, hmatch, ?_,
    U, hU, himage ▸ hPU, hfixU⟩
  intro i
  have hf (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
      frontier (D '' closedBall 0 1) = D '' sphere 0 1 := by
    have h := D.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  rw [← hf, ← hf, ← hmatch i]
  exact (Phi 1).toHomeomorph.image_frontier _



theorem closedSquare_subset_negative_ribbon
    {t a rho : Real} (ht : 0 < t) (hrho : 0 ≤ rho)
    (hrhoa : rho ≤ a) (hrhot : rho ^ 2 ≤ t) :
    closedSquare rho ⊆
      (fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
        (Icc (-a) a ×ˢ Icc 0 1) := by
  intro x hx
  change |x 0| ≤ rho ∧ |x 1| ≤ rho at hx
  let q := Real.sqrt (t + (x 1)^2)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = t + (x 1)^2 := Real.sq_sqrt (by positivity)
  have hrhoq : rho ≤ q := by nlinarith [sq_nonneg (x 1)]
  have hx0 : -q ≤ x 0 ∧ x 0 ≤ q := by
    have hh := abs_le.mp hx.1
    constructor <;> linarith [hh.1, hh.2]
  have hratio : -1 ≤ x 0 / q ∧ x 0 / q ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hq).mpr
      linarith [hx0.1]
    · apply (div_le_iff₀ hq).mpr
      linarith [hx0.2]
  refine ⟨(x 1, (x 0 / q + 1) / 2), ⟨abs_le.mp (hx.2.trans hrhoa),
    ⟨by linarith [hratio.1], by linarith [hratio.2]⟩⟩, ?_⟩
  change negativeLevelRibbon t (WithLp.toLp 2 ![x 1, (x 0 / q + 1) / 2]) = x
  ext i
  fin_cases i
  · change (2 * ((x 0 / q + 1) / 2) - 1) * q = x 0
    field_simp
    ring
  · rfl

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
