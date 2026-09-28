import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceRoots
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceRadialFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceCapGraph









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_outer_reference_cap_family :
    let I : Set ℝ := Ioo (-3 / 2) (3 / 2)
    let Jo : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
    let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
    let R : ℝ → ℝ → ℝ := fun t r =>
      r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
    let U : E2 → ℝ := fun y =>
      ‖y‖ ^ 2 + Real.sqrt (1 - ‖y‖ ^ 2) + y 0 / 32
    ∃ rho : ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ rho (I ×ˢ Jo) ∧
      (∀ p ∈ I ×ˢ Jo,
        Real.sqrt 15 / 4 < rho p ∧ rho p < Real.sqrt 4095 / 64 ∧
        R p.1 (rho p) = p.2 ∧ ∀ r ∈ Icc (rho p) 1, R p.1 r ≤ p.2) ∧
      ∃ F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
        ContDiff ℝ ∞ (fun p : E2 × ℝ => F p.2 p.1) ∧
        ContDiff ℝ ∞ (fun p : E2 × ℝ => (F p.2).symm p.1) ∧
        (∃ K : Set E2, IsCompact K ∧
          K ⊆ {v : E2 | 1 / 8 < ‖v‖ ∧ ‖v‖ < 4} ∧
          ∀ h : ℝ,
            tsupport (fun v : E2 => F h v - v) ⊆ K ∧
            tsupport (fun v : E2 => (F h).symm v - v) ⊆ K) ∧
        (∀ (h : ℝ) (v : E2), ‖v‖ ≤ 1 / 8 → F h v = v ∧ (F h).symm v = v) ∧
        (∀ h ∈ J,
          F h '' ball (0 : E2) 1 = {v : E2 | ‖v‖ < rho (v 0 / ‖v‖, h)} ∧
          F h '' closedBall (0 : E2) 1 = {v : E2 | ‖v‖ ≤ rho (v 0 / ‖v‖, h)} ∧
          F h '' sphere (0 : E2) 1 = {v : E2 | ‖v‖ = rho (v 0 / ‖v‖, h)}) ∧
        ∀ (h lambda : ℝ), |h - 17 / 16| ≤ 1 / 32768 →
          0 < lambda → lambda < 1 / 131072 →
          let a := stackCanonicalHorizontal (1 / 4) (1 / 2)
          let b := stackCanonicalVertical (1 / 4) (1 / 2)
          let M := stackCapProfilePath a a b b 0
          let N : UnitTwoSphere → E2 × ℝ := fun p =>
            let m := M (heightCoordinates (p : E3))
            (F (h + lambda * m.2) m.1, h + lambda * m.2)
          let Qplus : Set UnitTwoSphere :=
            {p | 0 ≤ (heightCoordinates (p : E3)).2}
          let B : Set E2 := F h '' closedBall (0 : E2) 1
          ∃ (V : Set E2) (g D : E2 → ℝ),
            IsOpen V ∧ B ⊆ V ∧ ContDiffOn ℝ ∞ g V ∧
            B ⊆ ball (0 : E2) (Real.sqrt 4095 / 64) ∧
            N '' Qplus = (fun y : E2 => (y, g y)) '' B ∧
            (∀ y ∈ B, h ≤ g y ∧ g y ≤ h + lambda) ∧
            (∀ y ∈ F h '' ball (0 : E2) 1, h < g y) ∧
            ContDiff ℝ ∞ D ∧ HasCompactSupport D ∧
            tsupport D ⊆ F h '' ball (0 : E2) 1 ∧ ∀ y ∈ B, D y = g y - U y := by
  let I : Set ℝ := Ioo (-3 / 2) (3 / 2)
  let Jo : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  let R : ℝ → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  let U : E2 → ℝ := fun y =>
    ‖y‖ ^ 2 + Real.sqrt (1 - ‖y‖ ^ 2) + y 0 / 32
  obtain ⟨ri, rho, _hri, hrho, hroots⟩ := exists_smooth_roots_in_height_window
  change ContDiffOn ℝ ∞ rho (I ×ˢ Jo) at hrho
  obtain ⟨hr0, _, hr1, _, _, _⟩ := radial_estimates
  have houter (p : ℝ × ℝ) (hp : p ∈ I ×ˢ Jo) :
      Real.sqrt 15 / 4 < rho p ∧ rho p < Real.sqrt 4095 / 64 ∧
      R p.1 (rho p) = p.2 ∧ ∀ r ∈ Icc (rho p) 1, R p.1 r ≤ p.2 := by
    obtain ⟨_, _, hlo, hhi, _, heq, hsign, _, _, _, _⟩ := hroots p hp
    refine ⟨hlo, hhi, heq, ?_⟩
    intro r hr
    rcases eq_or_lt_of_le hr.1 with he | hl
    · rw [← he]
      exact heq.le
    · exact ((hsign r ⟨by linarith only [hr0, hlo, hr.1], hr.2⟩).2.1.mpr
        (Or.inr hl)).le
  have hRootNeg (p : ℝ × ℝ) (hp : p ∈ I ×ˢ Jo) :
      deriv (fun a : ℝ => rho (p.1, a)) p.2 < 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, hneg, _, hd⟩ := hroots p hp
    rw [hd.deriv]
    exact inv_lt_zero.mpr (hneg.trans (by norm_num))
  have hsub : Icc (-1 : ℝ) 1 ×ˢ Jo ⊆ I ×ˢ Jo := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hbound (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ Jo) :
      1 / 4 < rho p ∧ rho p < 2 := by
    have hb := houter p (hsub hp)
    constructor <;> linarith only [hr0, hr1, hb.1, hb.2.1]
  obtain ⟨F, hF, hFi, hsupport, hfix, himages, hFamilyRay⟩ :=
    exists_joint_radial_filling rho hrho hbound
      (fun p hp => (hRootNeg p (hsub hp)).le)
  have hJJo : J ⊆ Jo := by
    intro a ha
    constructor <;> linarith [ha.1, ha.2]
  have hangle (e : E2) (he : ‖e‖ = 1) : e 0 ∈ I := by
    have hn : ‖e‖ ^ 2 = (e 0) ^ 2 + (e 1) ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rw [he] at hn
    constructor <;> nlinarith only [hn, sq_nonneg (e 1)]
  have hray (e : E2) (he : ‖e‖ = 1) : ∃ p : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ p ∧ (∀ a : ℝ, p (a, 0) = 0) ∧
      (∀ a r : ℝ, 0 < r → F a (r • e) = p (a, r) • e) ∧
      (∀ a r : ℝ, 0 < deriv (fun s : ℝ => p (a, s)) r) ∧
      (∀ a ∈ J, ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) a ≤ 0) ∧
      ∀ a ∈ J, deriv (fun s : ℝ => p (s, 1)) a < 0 := by
    obtain ⟨p, hp, hpm, hpray, hpu, hpr, hph⟩ := hFamilyRay e he
    refine ⟨p, hp, fun a => (hpm a).2, hpray, hpr, hph, ?_⟩
    intro a ha
    have hnear : (fun s : ℝ => p (s, 1)) =ᶠ[𝓝 a] (fun s : ℝ => rho (e 0, s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ha] with s hs
      exact hpu s hs
    rw [hnear.deriv_eq]
    exact hRootNeg (e 0, a) ⟨hangle e he, hJJo ha⟩
  have hroot (a : ℝ) (ha : a ∈ J) (e : E2) (he : ‖e‖ = 1) :
      ‖F a e‖ < Real.sqrt 4095 / 64 ∧ U (F a e) = a := by
    obtain ⟨p, _, _, hpray, hpu, _, _⟩ := hFamilyRay e he
    have hb := houter (e 0, a) ⟨hangle e he, hJJo ha⟩
    have hrp : 0 < rho (e 0, a) := by linarith only [hr0, hb.1]
    have hFe : F a e = rho (e 0, a) • e := by
      simpa only [one_smul, hpu a ha] using hpray a 1 (by norm_num)
    have hnorm : ‖F a e‖ = rho (e 0, a) := by
      rw [hFe, norm_smul, Real.norm_eq_abs, abs_of_pos hrp, he, mul_one]
    refine ⟨hnorm ▸ hb.2.1, ?_⟩
    change ‖F a e‖ ^ 2 + Real.sqrt (1 - ‖F a e‖ ^ 2) + (F a e) 0 / 32 = a
    rw [hnorm, hFe]
    exact hb.2.2.1
  refine ⟨rho, hrho, houter, F, hF, hFi, hsupport, hfix, himages, ?_⟩
  intro h lambda hh hlambda hsmall
  obtain ⟨e, _he, _hKe, _hes, _heis, htarget, hrad, hgs, _hgf, hgraph,
      hgbound, hgstrict, _hseam, D, hDs, hDc, hDsupp, hDformula⟩ :=
    exists_outer_cap_graph F hF (fun a x hx => (hfix a x hx).1) hray hroot
      h lambda hh hlambda hsmall
  exact ⟨e.target, _, D, e.open_target, htarget, hgs, hrad, hgraph,
    hgbound, hgstrict, hDs, hDc, hDsupp, hDformula⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
