import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Ribbon
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def horizontalCoordinates (b : Real) :
    Diffeomorph (𝓡 2) 𝓘(Real, Real × Real) E2 (Real × Real) ∞ where
  toFun x := (x 1, x 0 - b)
  invFun p := WithLp.toLp 2 ![b + p.2, p.1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv p := by ext <;> simp
  contMDiff_toFun := ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.prodMk
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.sub contDiff_const)).contMDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const.add contDiff_snd
    · exact contDiff_fst

private theorem exists_positive_morse_cap_squeeze
    {r t a ρ : Real} (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 < ρ) (hρa : ρ < a) (har : t + a ^ 2 < r ^ 2)
    (W : Set E2) (hW : IsOpen W)
    (hedge : ∀ s ∈ Icc (-a) a,
      (WithLp.toLp 2 ![Real.sqrt (t + s ^ 2), s] : E2) ∈ W) :
    ∃ K : Set E2, IsCompact K ∧
      K ⊆ {x | x ∈ openSquare r ∧ Real.sqrt (t + (x 1)^2) < x 0} ∧
      ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ K, F x = x) ∧
        (∀ x, F x 1 = x 1) ∧
        ∀ x, |x 1| ≤ ρ → Real.sqrt (t + (x 1)^2) ≤ x 0 → x 0 ≤ ρ →
          F x ∈ W ∧ Real.sqrt (t + (x 1)^2) ≤ F x 0 := by
  let h : Real → Real := fun s => Real.sqrt (t + s ^ 2)
  have hh : ContDiff Real ∞ h :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => ne_of_gt (by positivity))
  have ha : 0 < a := hρ.trans hρa
  have hrootr : h a < r := (Real.sqrt_lt (by positivity) hr.le).mpr har
  obtain ⟨b, hab, hbr⟩ := exists_between hrootr
  have hapos : a < h a := by
    have hs := Real.sq_sqrt (show 0 ≤ t + a ^ 2 by positivity)
    have hp := Real.sqrt_nonneg (t + a ^ 2)
    dsimp [h]
    nlinarith
  have hρb : ρ < b := hρa.trans (hapos.trans hab)
  let j : Real × Real → E2 := fun p => WithLp.toLp 2 ![h p.1 + p.2, p.1]
  have hj : Continuous j := by dsimp [j]; fun_prop
  have hbase : Icc (-a) a ×ˢ {(0 : Real)} ⊆ j ⁻¹' W := by
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hv0 : v = 0 := hv
    simpa [j, hv0] using hedge s hs
  obtain ⟨U, V, _, hV, hIU, h0V, hUV⟩ := generalized_tube_lemma
    isCompact_Icc isCompact_singleton (hW.preimage hj) hbase
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  let ε := min d ((b - h a) / 2)
  have hε : 0 < ε := lt_min hd (by linarith)
  have hεd : ε ≤ d := min_le_left _ _
  have hεb : h a + ε < b := by
    have := min_le_right d ((b - h a) / 2)
    dsimp [ε]
    linarith
  have hcollar (s v : Real) (hs : |s| ≤ a) (hv : 0 ≤ v ∧ v ≤ ε) :
      (WithLp.toLp 2 ![h s + v, s] : E2) ∈ W := by
    change (s, v) ∈ j ⁻¹' W
    apply hUV
    exact ⟨hIU (abs_le.mp hs), hdV (by
      rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hv.1]
      exact hv.2.trans hεd)⟩
  obtain ⟨c, hρc, hca⟩ := exists_between hρa
  let χ : ContDiffBump (0 : Real) := ⟨ρ, c, hρ, hρc⟩
  let q : Real → Real := fun s => χ s * (h s + ε - b)
  have hq : ContDiff Real ∞ q := χ.contDiff.mul ((hh.add contDiff_const).sub contDiff_const)
  have hqc : HasCompactSupport q := χ.hasCompactSupport.mul_right
  have hsc (s : Real) (hs : s ∈ tsupport q) : |s| ≤ c := by
    have hh : s ∈ tsupport χ := tsupport_mul_subset_left (f := χ) (g := fun s => h s + ε - b) hs
    rw [χ.tsupport_eq] at hh
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hh
  have hha (s : Real) (hs : |s| ≤ a) : h s ≤ h a := by
    apply Real.sqrt_le_sqrt
    have := abs_le.mp hs
    nlinarith [sq_nonneg (a - s), sq_nonneg (a + s)]
  let O : Set (Real × Real) := {p | |p.1| < a ∧ h p.1 < b + p.2 ∧ b + p.2 < r}
  have hO : IsOpen O :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      ((isOpen_lt (hh.continuous.comp continuous_fst) (continuous_const.add continuous_snd)).inter
        (isOpen_lt (continuous_const.add continuous_snd) continuous_const))
  have htrace (s : Real) (hs : s ∈ tsupport q) (u : Real) (hu : u ∈ Icc (0 : Real) 1) :
      (s, u * q s) ∈ O := by
    have hsa : |s| < a := (hsc s hs).trans_lt hca
    have hhs := hha s hsa.le
    have hneg : h s + ε - b < 0 := by linarith
    have hχ := χ.nonneg (x := s)
    have hχ1 := χ.le_one (x := s)
    have hc0 : 0 ≤ u * χ s := mul_nonneg hu.1 hχ
    have hc1 : u * χ s ≤ 1 := by nlinarith [hu.1, hu.2]
    have hlo := mul_le_mul_of_nonpos_right hc1 hneg.le
    have hhi := mul_nonpos_of_nonneg_of_nonpos hc0 hneg.le
    change |s| < a ∧ h s < b + u * (χ s * (h s + ε - b)) ∧
      b + u * (χ s * (h s + ε - b)) < r
    simp only [← mul_assoc]
    exact ⟨hsa, by constructor <;> linarith⟩
  obtain ⟨J, hJ, hJO, G, hGfirst, hGfix, hGgraph, _⟩ :=
    Rounding.exists_graph_push_within q hq hqc hO htrace
  let C := horizontalCoordinates b
  let F := (C.trans G).trans C.symm
  let K := C.symm '' J
  have hK : IsCompact K := hJ.image C.symm.continuous
  have hKO : K ⊆ {x | x ∈ openSquare r ∧ h (x 1) < x 0} := by
    rintro _ ⟨p, hp, rfl⟩
    have hh := hJO hp
    change |p.1| < a ∧ h p.1 < b + p.2 ∧ b + p.2 < r at hh
    change ((|b + p.2| < r ∧ |p.1| < r) ∧ h p.1 < b + p.2)
    have hp0 : 0 < b + p.2 := (Real.sqrt_pos.mpr (by positivity)).trans hh.2.1
    exact ⟨⟨by simpa only [abs_of_pos hp0] using hh.2.2,
      hh.1.trans (hapos.trans (hab.trans hbr))⟩, hh.2.1⟩
  have hfix (x : E2) (hx : x ∉ K) : F x = x := by
    have hn : C x ∉ J := fun h => hx ⟨C x, h, C.symm_apply_apply x⟩
    change C.symm (G (C x)) = x
    rw [hGfix _ hn, C.symm_apply_apply]
  have hfirst (x : E2) : F x 1 = x 1 := by
    change (G (C x)).1 = x 1
    rw [hGfirst]
    rfl
  refine ⟨K, hK, hKO, F, hfix, hfirst, ?_⟩
  intro x hx hxlo hxhi
  have hχx : χ (x 1) = 1 := χ.one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx)
  have hbottom : G (x 1, h (x 1) - b) = (x 1, h (x 1) - b) := by
    apply hGfix
    intro hm
    have hh := (hJO hm).2.1
    change h (x 1) < b + (h (x 1) - b) at hh
    linarith
  have hm := (strictMono_vertical_of_compact_support G.toHomeomorph hGfirst hJ hGfix (x 1)).monotone
  have hlo := hm (show h (x 1) - b ≤ x 0 - b by linarith)
  have hhi := hm (show x 0 - b ≤ 0 by linarith)
  change (G (x 1, h (x 1) - b)).2 ≤ (G (x 1, x 0 - b)).2 at hlo
  change (G (x 1, x 0 - b)).2 ≤ (G (x 1, 0)).2 at hhi
  rw [hbottom] at hlo
  rw [hGgraph] at hhi
  change h (x 1) - b ≤ (G (x 1, x 0 - b)).2 at hlo
  change (G (x 1, x 0 - b)).2 ≤ q (x 1) at hhi
  have hFx : F x 0 = b + (G (x 1, x 0 - b)).2 := rfl
  have hbounds : h (x 1) ≤ F x 0 ∧ F x 0 ≤ h (x 1) + ε := by
    dsimp [q] at hhi
    rw [hχx, one_mul] at hhi
    rw [hFx]
    constructor <;> linarith
  refine ⟨?_, hbounds.1⟩
  have heq : F x = WithLp.toLp 2 ![h (x 1) + (F x 0 - h (x 1)), x 1] := by
    ext i
    fin_cases i
    · simp
    · exact hfirst x
  rw [heq]
  exact hcollar _ _ (hx.trans hρa.le) ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩

private def reflectHorizontal : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![-x 0, x 1]
  invFun x := WithLp.toLp 2 ![-x 0, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.neg
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.neg
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

private theorem mem_compact_negative_ribbon_of_bounds
    {t a : Real} (ht : 0 < t) (x : E2) (hy : |x 1| ≤ a)
    (hx : |x 0| ≤ Real.sqrt (t + (x 1)^2)) :
    x ∈ ((fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-a) a ×ˢ Icc 0 1)) := by
  let d := Real.sqrt (t + (x 1)^2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hratio : |x 0 / d| ≤ 1 := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_one hd).mpr hx
  have hq : (x 0 / d + 1) / 2 ∈ Icc (0 : Real) 1 := by
    have h := abs_le.mp hratio
    constructor <;> linarith [h.1, h.2]
  refine ⟨(x 1, (x 0 / d + 1) / 2), ⟨abs_le.mp hy, hq⟩, ?_⟩
  ext i
  fin_cases i
  · change (2 * ((x 0 / d + 1) / 2) - 1) * d = x 0
    field_simp
    ring
  · rfl

theorem exists_morse_square_squeeze_into_ribbon_neighborhood
    {r t a ρ : Real} (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 < ρ) (hρa : ρ < a) (har : t + a ^ 2 < r ^ 2)
    (W : Set E2) (hW : IsOpen W)
    (hPW : ((fun z : Real × Real => negativeLevelRibbon t (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-a) a ×ˢ Icc 0 1)) ⊆ W) :
    ∃ K : Set E2, IsCompact K ∧
      K ⊆ openSquare r ∧ Disjoint K {x : E2 | -(x 0)^2 + (x 1)^2 = -t} ∧
      ∃ H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ K, H x = x) ∧
        (∀ x, |x 0| ≤ Real.sqrt (t + (x 1)^2) → H x = x) ∧
        H '' closedSquare ρ ⊆ W := by
  have hpos (s : Real) (hs : s ∈ Icc (-a) a) :
      (WithLp.toLp 2 ![Real.sqrt (t + s ^ 2), s] : E2) ∈ W := by
    apply hPW
    refine ⟨(s, 1), ⟨hs, by norm_num⟩, ?_⟩
    ext i
    fin_cases i <;> norm_num [negativeLevelRibbon, positiveLevelRibbon, saddleCoordinateSwap]
  have hneg (s : Real) (hs : s ∈ Icc (-a) a) :
      (WithLp.toLp 2 ![Real.sqrt (t + s ^ 2), s] : E2) ∈ reflectHorizontal ⁻¹' W := by
    apply hPW
    refine ⟨(s, 0), ⟨hs, by norm_num⟩, ?_⟩
    change negativeLevelRibbon t (WithLp.toLp 2 ![s, 0]) =
      WithLp.toLp 2 ![-Real.sqrt (t + s ^ 2), s]
    ext i
    fin_cases i <;> norm_num [negativeLevelRibbon, positiveLevelRibbon, saddleCoordinateSwap]
  obtain ⟨Kp, hKp, hKpO, Fp, hFpfix, hFpfirst, hFpcap⟩ :=
    exists_positive_morse_cap_squeeze hr ht hρ hρa har W hW hpos
  obtain ⟨Kn, hKn, hKnO, Fn, hFnfix, hFnfirst, hFncap⟩ :=
    exists_positive_morse_cap_squeeze hr ht hρ hρa har (reflectHorizontal ⁻¹' W)
      (hW.preimage reflectHorizontal.continuous) hneg
  let J := reflectHorizontal '' Kn
  let K := Kp ∪ J
  let Fm := (reflectHorizontal.trans Fn).trans reflectHorizontal
  let H := Fp.trans Fm
  have hreflection (x : E2) : reflectHorizontal (reflectHorizontal x) = x :=
    reflectHorizontal.symm_apply_apply x
  have hJ (x : E2) (hx : x ∈ J) :
      x ∈ openSquare r ∧ Real.sqrt (t + (x 1)^2) < -x 0 := by
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hKnO hy
    change (|-y 0| < r ∧ |y 1| < r) ∧ Real.sqrt (t + (y 1)^2) < - -y 0
    simpa only [Set.mem_ofPred_eq, openSquare, abs_neg, neg_neg] using h
  have hFmfix (x : E2) (hx : x ∉ J) : Fm x = x := by
    have hn : reflectHorizontal x ∉ Kn := fun hh => hx ⟨reflectHorizontal x, hh, hreflection x⟩
    change reflectHorizontal (Fn (reflectHorizontal x)) = x
    rw [hFnfix _ hn, hreflection]
  have hHfix (x : E2) (hx : x ∉ K) : H x = x := by
    change Fm (Fp x) = x
    rw [hFpfix x (fun h => hx (Or.inl h)), hFmfix x (fun h => hx (Or.inr h))]
  have hKsq : K ⊆ openSquare r := by
    rintro x (hx | hx)
    · exact (hKpO hx).1
    · exact (hJ x hx).1
  have hKlevel : Disjoint K {x : E2 | -(x 0)^2 + (x 1)^2 = -t} := by
    apply disjoint_left.mpr
    intro x hx heq
    have hs := Real.sq_sqrt (show 0 ≤ t + (x 1)^2 by positivity)
    have hp := Real.sqrt_nonneg (t + (x 1)^2)
    change -(x 0)^2 + (x 1)^2 = -t at heq
    rcases hx with hx | hx
    · have h := (hKpO hx).2
      nlinarith
    · have h := (hJ x hx).2
      nlinarith
  have hHmiddle (x : E2) (hx : |x 0| ≤ Real.sqrt (t + (x 1)^2)) : H x = x := by
    apply hHfix
    rintro (hp | hn)
    · exact (not_lt_of_ge ((le_abs_self _).trans hx)) (hKpO hp).2
    · exact (not_lt_of_ge ((neg_le_abs _).trans hx)) (hJ x hn).2
  refine ⟨K, hKp.union (hKn.image reflectHorizontal.continuous), hKsq, hKlevel,
    H, hHfix, hHmiddle, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : |x 0| ≤ ρ := hx.1
  have hx1 : |x 1| ≤ ρ := hx.2
  have hroot : 0 ≤ Real.sqrt (t + (x 1)^2) := Real.sqrt_nonneg _
  by_cases hp : Real.sqrt (t + (x 1)^2) ≤ x 0
  · have hcap := hFpcap x hx1 hp (le_abs_self _ |>.trans hx0)
    have hnot : Fp x ∉ J := by
      intro hh
      have h := (hJ (Fp x) hh).2
      rw [hFpfirst] at h
      linarith [hcap.2]
    change Fm (Fp x) ∈ W
    rw [hFmfix _ hnot]
    exact hcap.1
  · have hFpx : Fp x = x := hFpfix x (fun hh => hp (hKpO hh).2.le)
    change Fm (Fp x) ∈ W
    rw [hFpx]
    by_cases hn : Real.sqrt (t + (x 1)^2) ≤ -x 0
    · have hy1 : |reflectHorizontal x 1| ≤ ρ := hx1
      have hylo : Real.sqrt (t + (reflectHorizontal x 1)^2) ≤ reflectHorizontal x 0 := hn
      have hyhi : reflectHorizontal x 0 ≤ ρ := (neg_le_abs _).trans hx0
      exact (hFncap (reflectHorizontal x) hy1 hylo hyhi).1
    · have hFm : Fm x = x := hFmfix x (fun hh => hn (hJ x hh).2.le)
      rw [hFm]
      apply hPW
      apply mem_compact_negative_ribbon_of_bounds ht x (hx1.trans hρa.le)
      exact abs_le.mpr ⟨by linarith, (not_le.mp hp).le⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
