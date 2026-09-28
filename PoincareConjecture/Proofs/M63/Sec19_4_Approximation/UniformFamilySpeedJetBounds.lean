import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.UniformUpperCutoffJetBounds
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.NonconstantSpeedGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_uniform_c2_speed_jet_bounds [T2Space M]
    (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {tau R nu0 V0 B0 : ℝ} (hat : a < tau) (htb : tau < b)
    (hR : 0 ≤ R) (hnu0 : 0 < nu0) (hV0 : 0 ≤ V0) (hB0 : 0 ≤ B0) :
    ∃ K J m V G J1 J2 : ℝ,
      0 ≤ K ∧ CurveEvolutionAmbientBounds F K K K ∧
      0 ≤ J ∧ 0 < m ∧ 0 ≤ V ∧ 0 ≤ G ∧ 0 ≤ J1 ∧ 0 ≤ J2 ∧
      ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
        (∀ x, nu0 ≤ curveSpeed F c a x ∧ curveSpeed F c a x ≤ V0) →
        (∀ x, |deriv (curveSpeed F c a) x| ≤ B0) →
        (∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R) →
        (∀ t ∈ Ioo a b, ∀ x,
          (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
            J / Real.sqrt (t - a)) ∧
        (∀ t ∈ Icc a b, ∀ x,
          m ≤ curveSpeed F c t x ∧ curveSpeed F c t x ≤ V ∧
            |deriv (curveSpeed F c t) x| ≤ G) ∧
        (∀ t ∈ Ioo tau b, ∀ x,
          (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤ J1 ∧
          (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 2 t x) ≤ J2) := by
  have hab : a < b := hat.trans htb
  let H := b - a
  have hH : 0 ≤ H := (sub_pos.mpr hab).le
  obtain ⟨K, hK, hBounds, hRm, hRc⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  let A := 14 * R + 10 * K + 1
  let G0 := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
  let lam := 1 + A * H
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  let D := H * G0 + lam * D0
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hG0 : 0 ≤ G0 := by dsimp only [G0]; positivity
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let J := Real.sqrt (lam * R + D * H)
  let m := nu0 * Real.exp (-(K + R) * H)
  let V := V0 * Real.exp ((K + R) * H)
  let L := (K + 2 * K * Real.sqrt R) * H + 4 * Real.sqrt R * J * Real.sqrt H
  let G := V * (B0 / nu0 + V * L)
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hm : 0 < m := mul_pos hnu0 (Real.exp_pos _)
  have hV : 0 ≤ V := mul_nonneg hV0 (Real.exp_pos _).le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  obtain ⟨C1, _hC1, hcap1⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff F hcompact 1
    (le_refl a) hab (le_refl b) hR (sub_pos.mpr hat)
  obtain ⟨C2, _hC2, hcap2⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff F hcompact 2
    (le_refl a) hab (le_refl b) hR (sub_pos.mpr hat)
  refine ⟨K, J, m, V, G, Real.sqrt C1, Real.sqrt C2, hK, hBounds, hJ, hm,
    hV, hG, Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro c hc hinitial hgrad0 hcurv
  have hshort (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
        J / Real.sqrt (t - a) := by
    have hage : 0 < t - a := sub_pos.mpr ht.1
    have hageH : t - a ≤ H := sub_le_sub_right ht.2.le a
    have hb := m63FirstJetSquared_short_time_bound F c hc hK hR hBounds
      hRm hRc hcurv hH x t ht hageH
    change m63CurvatureJetSquared F c 1 t x ≤ lam * R / (t - a) + D at hb
    have hf : lam * R / (t - a) + D ≤ (lam * R + D * H) / (t - a) := by
      apply (le_div_iff₀ hage).mpr
      rw [add_mul, div_mul_cancel₀ _ hage.ne']
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hageH hD)
    change Real.sqrt (m63CurvatureJetSquared F c 1 t x) ≤
      Real.sqrt (lam * R + D * H) / Real.sqrt (t - a)
    exact (Real.sqrt_le_sqrt (hb.trans hf)).trans_eq
      (Real.sqrt_div (add_nonneg (mul_nonneg hlam hR) (mul_nonneg hD hH)) _)
  have hspeed (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      m ≤ curveSpeed F c t x ∧ curveSpeed F c t x ≤ V := by
    have hb := curveSpeed_exp_bounds F c hc hBounds x (fun r hr => hcurv r hr x)
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) ht ht.1
    have hage : t - a ≤ H := sub_le_sub_right ht.2 a
    have hexp := mul_le_mul_of_nonneg_left hage (add_nonneg hK hR)
    constructor
    · calc
        m ≤ nu0 * Real.exp (-(K + R) * (t - a)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hnu0.le
        _ ≤ curveSpeed F c a x * Real.exp (-(K + R) * (t - a)) :=
          mul_le_mul_of_nonneg_right (hinitial x).1 (Real.exp_pos _).le
        _ ≤ curveSpeed F c t x := hb.1
    · calc
        curveSpeed F c t x ≤ curveSpeed F c a x * Real.exp ((K + R) * (t - a)) := hb.2
        _ ≤ V0 * Real.exp ((K + R) * (t - a)) :=
          mul_le_mul_of_nonneg_right (hinitial x).2 (Real.exp_pos _).le
        _ ≤ V := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hV0
  have hgrad (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      |deriv (curveSpeed F c t) x| ≤ G := by
    have hb := (curveSpeed_spatial_ratio_integral_of_speed_le F c hc hK hR hJ hV
      hBounds (fun r hr y => (hspeed r (Ioo_subset_Icc_self hr) y).2)
      hcurv hshort ht x).2.2
    have hv : 0 < curveSpeed F c t x := speed_pos F c hc ht x
    have hv0 : 0 < curveSpeed F c a x := hnu0.trans_le (hinitial x).1
    have hratio0 : |deriv (curveSpeed F c a) x / curveSpeed F c a x| ≤ B0 / nu0 := by
      rw [abs_div, abs_of_pos hv0]
      exact (div_le_div_of_nonneg_right (hgrad0 x) hv0.le).trans
        (div_le_div_of_nonneg_left hB0 hnu0 (hinitial x).1)
    have hage : t - a ≤ H := sub_le_sub_right ht.2 a
    have hlin : 0 ≤ K + 2 * K * Real.sqrt R := by positivity
    have hroot : 0 ≤ 4 * Real.sqrt R * J := by positivity
    have hincrement : |deriv (curveSpeed F c t) x / curveSpeed F c t x -
        deriv (curveSpeed F c a) x / curveSpeed F c a x| ≤ V * L :=
      hb.trans (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hage hlin)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hage) hroot)) hV)
    have hratio : |deriv (curveSpeed F c t) x / curveSpeed F c t x| ≤
        B0 / nu0 + V * L := by
      calc
        _ = |(deriv (curveSpeed F c t) x / curveSpeed F c t x -
            deriv (curveSpeed F c a) x / curveSpeed F c a x) +
              deriv (curveSpeed F c a) x / curveSpeed F c a x| := by rw [sub_add_cancel]
        _ ≤ |deriv (curveSpeed F c t) x / curveSpeed F c t x -
            deriv (curveSpeed F c a) x / curveSpeed F c a x| +
              |deriv (curveSpeed F c a) x / curveSpeed F c a x| := abs_add_le _ _
        _ ≤ V * L + B0 / nu0 := add_le_add hincrement hratio0
        _ = B0 / nu0 + V * L := add_comm _ _
    calc
      |deriv (curveSpeed F c t) x| =
          |deriv (curveSpeed F c t) x / curveSpeed F c t x| * curveSpeed F c t x := by
        rw [abs_div, abs_of_pos hv, div_mul_cancel₀ _ hv.ne']
      _ ≤ (B0 / nu0 + V * L) * V :=
        mul_le_mul hratio (hspeed t ht x).2 hv.le
          (add_nonneg (div_nonneg hB0 hnu0.le) (mul_nonneg hV hL))
      _ = G := by dsimp only [G]; ring
  refine ⟨hshort, fun t ht x => ⟨(hspeed t ht x).1, (hspeed t ht x).2, hgrad t ht x⟩, ?_⟩
  intro t ht x
  have hct : t ∈ Ioo a b := ⟨hat.trans ht.1, ht.2⟩
  have hage : tau - a ≤ t - a := sub_le_sub_right ht.1.le a
  have hz : ∀ r ∈ Ioo a b, ∀ y, m63CurvatureJetSquared F c 0 r y ≤ R := hcurv
  have hcs : M63SmoothShrinkingCurveOn F c (Icc a b) := m63SmoothClosed_iff_m62.mpr hc
  exact ⟨Real.sqrt_le_sqrt (hcap1 b hab le_rfl c hcs hz t hct hage x),
    Real.sqrt_le_sqrt (hcap2 b hab le_rfl c hcs hz t hct hage x)⟩

end PoincareConjecture.M63
