import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseArcCuts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_straight_join_local_geometry
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A B c eta : ℝ} (heta : 0 < eta) (hc : 0 < c)
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A) :
    ∃ epsilon > 0, epsilon < eta ∧
      (∀ t ∈ Icc (A - epsilon) A,
        0 < inner ℝ (deriv alpha A) (deriv alpha t) ∧
        0 < inner ℝ (quarterTurn (deriv alpha t)) (quarterTurn (deriv alpha A))) ∧
      (∀ t ∈ Icc B (B + epsilon),
        0 < inner ℝ (deriv alpha A) (deriv beta t) ∧
        0 < inner ℝ (quarterTurn (deriv beta t)) (quarterTurn (deriv alpha A))) ∧
      InjOn alpha (Icc (A - epsilon) A) ∧ InjOn beta (Icc B (B + epsilon)) ∧
      ∀ s ∈ Icc (A - epsilon) A, ∀ t ∈ Icc B (B + epsilon),
        alpha s = beta t → s = A ∧ t = B := by
  have hac : Continuous (deriv alpha) := (contDiff_infty_iff_deriv.mp ha).2.continuous
  have hbc : Continuous (deriv beta) := (contDiff_infty_iff_deriv.mp hb).2.continuous
  have hv : 0 < inner ℝ (deriv alpha A) (deriv alpha A) := real_inner_self_pos.mpr hreg
  have hw : 0 < inner ℝ (quarterTurn (deriv alpha A)) (quarterTurn (deriv alpha A)) := by
    apply real_inner_self_pos.mpr
    intro hz
    exact hreg (quarterTurn.injective (by simpa using hz))
  let P : Set ℝ := {s |
    (0 < inner ℝ (deriv alpha A) (deriv alpha (A + s)) ∧
      0 < inner ℝ (quarterTurn (deriv alpha (A + s))) (quarterTurn (deriv alpha A))) ∧
    (0 < inner ℝ (deriv alpha A) (deriv beta (B + s)) ∧
      0 < inner ℝ (quarterTurn (deriv beta (B + s))) (quarterTurn (deriv alpha A)))}
  have hP : IsOpen P := by
    have hca : Continuous (fun s : ℝ => deriv alpha (A + s)) :=
      hac.comp (continuous_const.add continuous_id)
    have hcb : Continuous (fun s : ℝ => deriv beta (B + s)) :=
      hbc.comp (continuous_const.add continuous_id)
    have hpa := isOpen_lt (continuous_const (y := (0 : ℝ)))
      ((continuous_const (y := deriv alpha A)).inner hca)
    have hta := isOpen_lt (continuous_const (y := (0 : ℝ)))
      ((quarterTurn.continuous.comp hca).inner
        (continuous_const (y := quarterTurn (deriv alpha A))))
    have hpb := isOpen_lt (continuous_const (y := (0 : ℝ)))
      ((continuous_const (y := deriv alpha A)).inner hcb)
    have htb := isOpen_lt (continuous_const (y := (0 : ℝ)))
      ((quarterTurn.continuous.comp hcb).inner
        (continuous_const (y := quarterTurn (deriv alpha A))))
    exact (hpa.inter hta).inter (hpb.inter htb)
  have hzero : (0 : ℝ) ∈ P := by
    refine ⟨⟨by simpa using hv, by simpa using hw⟩, ?_, ?_⟩
    · simp only [add_zero, htan, real_inner_smul_right]
      exact mul_pos hc hv
    · simp only [add_zero, htan, map_smul, real_inner_smul_left]
      exact mul_pos hc hw
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hzero)
  let epsilon := min eta r / 2
  have he : 0 < epsilon := half_pos (lt_min heta hr)
  have hemin : epsilon < min eta r := half_lt_self (lt_min heta hr)
  have heeta : epsilon < eta := hemin.trans_le (min_le_left _ _)
  have her : epsilon < r := hemin.trans_le (min_le_right _ _)
  have hsmall (s : ℝ) (hs : |s| ≤ epsilon) : s ∈ P := by
    apply hball
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs.trans_lt her
  have hleft (t : ℝ) (ht : t ∈ Icc (A - epsilon) A) :
      0 < inner ℝ (deriv alpha A) (deriv alpha t) ∧
      0 < inner ℝ (quarterTurn (deriv alpha t)) (quarterTurn (deriv alpha A)) := by
    have hs := (hsmall (t - A) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1
    simpa only [add_sub_cancel] using hs
  have hright (t : ℝ) (ht : t ∈ Icc B (B + epsilon)) :
      0 < inner ℝ (deriv alpha A) (deriv beta t) ∧
      0 < inner ℝ (quarterTurn (deriv beta t)) (quarterTurn (deriv alpha A)) := by
    have hs := (hsmall (t - B) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
    simpa only [add_sub_cancel] using hs
  let f : ℝ → ℝ := fun t => inner ℝ (deriv alpha A) (alpha t)
  let g : ℝ → ℝ := fun t => inner ℝ (deriv alpha A) (beta t)
  have hfd (t : ℝ) : deriv f t = inner ℝ (deriv alpha A) (deriv alpha t) := by
    simpa only [inner_zero_left, add_zero] using
      ((hasDerivAt_const t (deriv alpha A)).inner ℝ
      ((ha.differentiable (by simp)) t).hasDerivAt).deriv
  have hgd (t : ℝ) : deriv g t = inner ℝ (deriv alpha A) (deriv beta t) := by
    simpa only [inner_zero_left, add_zero] using
      ((hasDerivAt_const t (deriv alpha A)).inner ℝ
      ((hb.differentiable (by simp)) t).hasDerivAt).deriv
  have hfc : Continuous f := continuous_const.inner ha.continuous
  have hgc : Continuous g := continuous_const.inner hb.continuous
  have hfm : StrictMonoOn f (Icc (A - epsilon) A) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hfc.continuousOn
      (fun t ht => by rw [hfd]; exact (hleft t (interior_subset ht)).1)
  have hgm : StrictMonoOn g (Icc B (B + epsilon)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hgc.continuousOn
      (fun t ht => by rw [hgd]; exact (hright t (interior_subset ht)).1)
  have hAmem : A ∈ Icc (A - epsilon) A := ⟨by linarith, le_rfl⟩
  have hBmem : B ∈ Icc B (B + epsilon) := ⟨le_rfl, by linarith⟩
  have hfg : f A = g B := congrArg (inner ℝ (deriv alpha A)) hend
  refine ⟨epsilon, he, heeta, hleft, hright, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact hfm.injOn hs ht (congrArg (inner ℝ (deriv alpha A)) hst)
  · intro s hs t ht hst
    exact hgm.injOn hs ht (congrArg (inner ℝ (deriv alpha A)) hst)
  · intro s hs t ht hst
    have hval : f s = g t := congrArg (inner ℝ (deriv alpha A)) hst
    have hle := hfm.monotoneOn hs hAmem hs.2
    have hle' := hgm.monotoneOn hBmem ht ht.1
    exact ⟨hfm.injOn hs hAmem (by linarith), hgm.injOn ht hBmem (by linarith)⟩

end PoincareConjecture
