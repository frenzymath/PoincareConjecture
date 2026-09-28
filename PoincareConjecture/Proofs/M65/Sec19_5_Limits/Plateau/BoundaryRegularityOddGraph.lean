import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityReflection
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal LineDeriv

namespace PoincareConjecture.M65Boundary

private theorem odd_transition_bound :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t, |deriv Real.smoothTransition t| ≤ B) ∧
      ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition t = 0 := by
  have hc := (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  have hz (t : ℝ) (ht : t ∉ Icc (0 : ℝ) 1) : deriv Real.smoothTransition t = 0 := by
    by_cases h : t < 0
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [gt_mem_nhds h] with x hx
        exact Real.smoothTransition.zero_of_nonpos hx.le
      rw [he.deriv_eq, deriv_const]
    · have h' : 1 < t := lt_of_not_ge (fun hh => ht ⟨le_of_not_gt h, hh⟩)
      have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [lt_mem_nhds h'] with x hx
        exact Real.smoothTransition.one_of_one_le hx.le
      rw [he.deriv_eq, deriv_const]
  refine ⟨max B 0, le_max_right _ _, ?_, hz⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (show |deriv Real.smoothTransition t| ≤ B from hB t ht).trans (le_max_left _ _)
  · rw [hz t ht, abs_zero]; exact le_max_right _ _

private def oddCutoff (n : ℕ) (z : LoopPlane) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * z 1 - 1)

private theorem oddCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (oddCutoff n) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff).sub
      contDiff_const)

private def oddTest (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
    (n : ℕ) : 𝓢(LoopPlane, ℝ) :=
  (hc.mul_left (f := oddCutoff n)).toSchwartzMap
    ((oddCutoff_smooth n).mul (test.smooth (⊤ : ℕ∞)))

private theorem oddTest_properties (test : 𝓢(LoopPlane, ℝ))
    (hc : HasCompactSupport test) {R : ℝ} (hs : tsupport test ⊆ ball (0 : LoopPlane) R) :
    (∀ n, HasCompactSupport (oddTest test hc n) ∧
      tsupport (oddTest test hc n) ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1}) ∧
    (∀ n z i, fderiv ℝ (oddTest test hc n) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      oddCutoff n z * fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) +
        deriv Real.smoothTransition (((n : ℝ) + 1) * z 1 - 1) * ((n : ℝ) + 1) *
          (EuclideanSpace.basisFun (Fin 2) ℝ i) 1 * test z) ∧
    ∀ z : LoopPlane, 0 < z 1 → Tendsto (fun n => oddCutoff n z) atTop (𝓝 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hsub : tsupport (oddTest test hc n) ⊆ tsupport test := tsupport_mul_subset_right
    have hheight : tsupport (oddTest test hc n) ⊆ {z : LoopPlane | 1 ≤ ((n : ℝ) + 1) * z 1} := by
      apply closure_minimal
      · intro z hz
        by_contra h
        apply hz
        change oddCutoff n z * test z = 0
        rw [show oddCutoff n z = 0 from Real.smoothTransition.zero_of_nonpos
          (by change ¬1 ≤ ((n : ℝ) + 1) * z 1 at h; linarith [not_le.mp h]), zero_mul]
      · exact isClosed_le continuous_const
          (continuous_const.mul (EuclideanSpace.proj 1).continuous)
    refine ⟨hc.mul_left, fun z hz => ⟨hs (hsub hz), ?_⟩⟩
    have hh : 1 ≤ ((n : ℝ) + 1) * z 1 := hheight hz
    have hk : 0 < (n : ℝ) + 1 := by positivity
    change 0 < z 1
    nlinarith
  · intro n z i
    have hl := ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := z)).const_mul
      ((n : ℝ) + 1) |>.sub_const 1
    have hh := (Real.smoothTransition.contDiffAt (x := ((n : ℝ) + 1) * z 1 - 1)
      (n := 1)).differentiableAt one_ne_zero |>.hasDerivAt
    have hp := (hh.comp_hasFDerivAt z hl).mul test.differentiableAt.hasFDerivAt
    change fderiv ℝ ((Real.smoothTransition ∘ fun w : LoopPlane =>
      ((n : ℝ) + 1) * w 1 - 1) * (test : LoopPlane → ℝ)) z _ = _
    have he := hp.fderiv
    simp only [EuclideanSpace.proj, PiLp.proj_apply] at he
    rw [he]
    simp only [add_apply, smul_apply, smul_eq_mul, PiLp.proj_apply, Function.comp_apply,
      oddCutoff]
    ring
  · intro z hz
    apply tendsto_const_nhds.congr'
    obtain ⟨n0, hn0⟩ := exists_nat_gt (2 / z 1)
    filter_upwards [eventually_ge_atTop n0] with n hn
    have hh := (div_lt_iff₀ hz).mp hn0
    have hnn : (n0 : ℝ) ≤ n := Nat.cast_le.mpr hn
    exact (Real.smoothTransition.one_of_one_le (by nlinarith) : oddCutoff n z = 1).symm

private theorem odd_strip_volume {R a : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) :
    volume.real {z : LoopPlane | |z 0| ≤ R ∧ z 1 ∈ Icc (0 : ℝ) a} = 2 * R * a := by
  let l : Fin 2 → ℝ := ![-R, 0]
  let u : Fin 2 → ℝ := ![R, a]
  have he : {z : LoopPlane | |z 0| ≤ R ∧ z 1 ∈ Icc (0 : ℝ) a} =
      WithLp.ofLp ⁻¹' Icc l u := by
    ext z
    simp [l, u, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, abs_le, and_assoc, and_left_comm]
  rw [he, (PiLp.volume_preserving_ofLp (Fin 2)).measureReal_preimage
    measurableSet_Icc.nullMeasurableSet]
  change (volume (Icc l u)).toReal = _
  rw [Real.volume_Icc_pi_toReal (by intro i; fin_cases i <;> simp [l, u] <;> linarith)]
  simp only [l, u, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero, sub_neg_eq_add]
  ring

private theorem odd_error_tendsto {R beta H : ℝ} (hR : 0 < R) (hb : 0 < beta)
    (hH : 0 ≤ H) (u : LoopPlane → ℝ)
    (hheight : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      |u z| ≤ H * (z 1) ^ beta) (test : 𝓢(LoopPlane, ℝ)) :
    Tendsto (fun n : ℕ => ∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      deriv Real.smoothTransition (((n : ℝ) + 1) * z 1 - 1) * ((n : ℝ) + 1) *
        test z * u z) atTop (𝓝 0) := by
  obtain ⟨B, hB, hBD, hzero⟩ := odd_transition_bound
  let V := SchwartzMap.seminorm ℝ 0 0 test
  have hV : 0 ≤ V := apply_nonneg _ _
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hbound (n : ℕ) : ‖∫ z in U,
      deriv Real.smoothTransition (((n : ℝ) + 1) * z 1 - 1) * ((n : ℝ) + 1) *
        test z * u z‖ ≤ 4 * R * B * V * H * (2 / ((n : ℝ) + 1)) ^ beta := by
    let k := (n : ℝ) + 1
    let a := 2 / k
    let S := U ∩ {z : LoopPlane | z 1 ≤ a}
    let Q := {z : LoopPlane | |z 0| ≤ R ∧ z 1 ∈ Icc (0 : ℝ) a}
    have hk : 0 < k := by dsimp only [k]; positivity
    have ha : 0 ≤ a := by dsimp only [a]; positivity
    have hSQ : S ⊆ Q := by
      intro z hz
      exact ⟨(PiLp.norm_apply_le z 0).trans (mem_ball_zero_iff.mp hz.1.1).le,
        hz.1.2.le, hz.2⟩
    have hQ : IsCompact Q := by
      have he : Q = WithLp.ofLp ⁻¹' Icc (![-R, 0] : Fin 2 → ℝ) ![R, a] := by
        ext z
        simp [Q, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, abs_le, and_assoc, and_left_comm]
      rw [he]
      exact (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).isCompact_preimage.mpr isCompact_Icc
    have hvol : volume.real S ≤ 2 * R * a := by
      rw [← odd_strip_volume hR.le ha]
      exact measureReal_mono hSQ hQ.measure_lt_top.ne
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU inter_subset_left (by
      intro z hz
      have hz' : a < z 1 := lt_of_not_ge (fun hh => hz.2 ⟨hz.1, hh⟩)
      have hn : ((n : ℝ) + 1) * z 1 - 1 ∉ Icc (0 : ℝ) 1 := by
        have hh := (div_lt_iff₀ hk).mp hz'
        intro hm
        dsimp only [k] at hh
        linarith [hm.2]
      rw [hzero _ hn, zero_mul, zero_mul, zero_mul])]
    calc
      _ ≤ (B * k * V * (H * a ^ beta)) * volume.real S := by
        apply norm_setIntegral_le_of_norm_le_const
          ((measure_mono hSQ).trans_lt hQ.measure_lt_top)
        intro z hz
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hk]
        have hu : |u z| ≤ H * a ^ beta := (hheight z hz.1).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1.2.le hz.2 hb.le) hH)
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (hBD _) hk.le)
          (test.norm_le_seminorm ℝ z) (abs_nonneg _) (by positivity)) hu
          (abs_nonneg _) (by positivity)
      _ ≤ (B * k * V * (H * a ^ beta)) * (2 * R * a) :=
        mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = (2 * R * B * V * H * a ^ beta) * (k * a) := by ring
      _ = _ := by
        rw [show k * a = 2 by dsimp only [a]; field_simp]
        change (2 * R * B * V * H * a ^ beta) * 2 = 4 * R * B * V * H * a ^ beta
        ring
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  have hp := (ht.rpow_const_nhds_zero hb).const_mul (4 * R * B * V * H)
  rw [mul_zero] at hp
  exact squeeze_zero_norm hbound hp

private theorem oddCutoff_integral_tendsto {R : ℝ} {g : LoopPlane → ℝ}
    (hg : IntegrableOn g (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})) :
    Tendsto (fun n => ∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, oddCutoff n z * g z)
      atTop (𝓝 (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, g z)) := by
  have hU : MeasurableSet (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}) :=
    measurableSet_ball.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  apply tendsto_integral_of_dominated_convergence (fun z => ‖g z‖)
  · exact fun n => (oddCutoff_smooth n).continuous.aestronglyMeasurable.mul hg.1
  · exact hg.norm
  · intro n
    exact ae_of_all _ fun z => by
      rw [norm_mul, Real.norm_eq_abs, oddCutoff,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [ae_restrict_mem hU] with z hz
    have ht := (oddTest_properties (0 : 𝓢(LoopPlane, ℝ))
      (by change IsCompact (tsupport (fun _ : LoopPlane => (0 : ℝ))); simp)
      (R := R) (by simp)).2.2 z hz.2
    simpa only [one_mul] using ht.mul_const (g z)

private theorem odd_half_weak {R beta H : ℝ} (hR : 0 < R) (hb : 0 < beta) (hH : 0 ≤ H)
    (u d : LoopPlane → ℝ) (i : Fin 2)
    (hu : MemLp u 2 (volume.restrict (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})))
    (hd : MemLp d 2 (volume.restrict (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})))
    (hheight : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, |u z| ≤ H * (z 1) ^ beta)
    (hw : ∀ test : 𝓢(LoopPlane, ℝ), HasCompactSupport test →
      tsupport test ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} →
      (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, test z * d z) =
        -(∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * u z))
    (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
    (hs : tsupport test ⊆ ball (0 : LoopPlane) R) :
    (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, test z * d z) =
      -(∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * u z) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  let dt : 𝓢(LoopPlane, ℝ) := ∂_{v} test
  have hdt (z : LoopPlane) : dt z = fderiv ℝ test z v := rfl
  have hl := (test.memLp 2 volume).restrict U |>.integrable_mul hd
  have hr : IntegrableOn (fun z => fderiv ℝ test z v * u z) U :=
    (dt.memLp 2 volume).restrict U |>.integrable_mul hu
  obtain ⟨hts, hder, _⟩ := oddTest_properties test hc hs
  have hchi (n : ℕ) (z : LoopPlane) : ‖oddCutoff n z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, oddCutoff, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hbase (n : ℕ) : IntegrableOn (fun z => oddCutoff n z * (fderiv ℝ test z v * u z)) U :=
    hr.bdd_mul (oddCutoff_smooth n).continuous.aestronglyMeasurable (ae_of_all _ (hchi n))
  let err := fun (n : ℕ) (z : LoopPlane) => deriv Real.smoothTransition (((n : ℝ) + 1) * z 1 - 1) *
    ((n : ℝ) + 1) * test z * u z
  have he (n : ℕ) : IntegrableOn (fun z => (v 1) * err n z) U := by
    have ht := ((∂_{v} (oddTest test hc n)).memLp 2 volume).restrict U |>.integrable_mul hu
    apply (ht.sub (hbase n)).congr
    exact ae_of_all _ fun z => by
      change fderiv ℝ (oddTest test hc n) z v * u z - _ = _
      rw [hder]; dsimp only [v, err]; ring
  have heq (n : ℕ) : (∫ z in U, oddCutoff n z * (test z * d z)) =
      -((∫ z in U, oddCutoff n z * (fderiv ℝ test z v * u z)) + (v 1) * ∫ z in U, err n z) := by
    have hw' := hw (oddTest test hc n) (hts n).1 (hts n).2
    have hl' : (∫ z in U, oddCutoff n z * (test z * d z)) =
        ∫ z in U, oddTest test hc n z * d z := integral_congr_ae (ae_of_all _ fun z => by
          change oddCutoff n z * (test z * d z) = (oddCutoff n z * test z) * d z
          ring)
    rw [hl', hw']
    congr 1
    rw [← integral_const_mul, ← integral_add (hbase n) (he n)]
    exact integral_congr_ae (ae_of_all _ fun z => by
      dsimp only []; rw [hder]; dsimp only [v, err]; ring)
  have ht := ((oddCutoff_integral_tendsto hr).add
    ((odd_error_tendsto hR hb hH u hheight test).const_mul (v 1))).neg
  simp only [mul_zero, add_zero] at ht
  exact tendsto_nhds_unique (oddCutoff_integral_tendsto hl) (ht.congr (fun n => (heq n).symm))

private theorem odd_height_bound {N : ℕ} {R beta H : ℝ} (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hh : ∀ x ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ∀ y ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ‖u y - u x‖ ≤ H * dist y x ^ beta)
    (hz : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}, z 1 = 0 → u z = 0) :
    ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}, ‖u z‖ ≤ H * (z 1) ^ beta := by
  intro z hm
  let y := z 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0
  have hy : y ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} := by
    constructor
    · rw [mem_closedBall_zero_iff]
      simpa only [y, norm_smul, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one]
        using (PiLp.norm_apply_le z 0).trans (mem_closedBall_zero_iff.mp hm.1)
    · simp [y, EuclideanSpace.basisFun_apply]
  have hy0 : y 1 = 0 := by simp [y, EuclideanSpace.basisFun_apply]
  have hd : dist z y = z 1 := by
    rw [dist_eq_norm, show z - y = z 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 by
      ext i; fin_cases i <;> simp [y, EuclideanSpace.basisFun_apply], norm_smul,
      (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hm.2]
  simpa only [hz y hy hy0, sub_zero, hd] using hh y hy z hm

private theorem odd_integral_split {R : ℝ} {f : LoopPlane → ℝ}
    (hf : IntegrableOn f (ball (0 : LoopPlane) R)) :
    (∫ z in ball (0 : LoopPlane) R, f z) =
      (∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f z) +
      ∫ z in ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, f (boundaryPlaneReflection z) := by
  have hnull : volume {z : LoopPlane | z 1 = 0} = 0 := by
    let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 1
    change volume (LinearMap.ker L.toLinearMap : Set LoopPlane) = 0
    apply Measure.addHaar_submodule
    intro htop
    have hm : EuclideanSpace.basisFun (Fin 2) ℝ 1 ∈ LinearMap.ker L.toLinearMap := by
      rw [htop]; trivial
    norm_num [L, LinearMap.mem_ker, EuclideanSpace.basisFun_apply] at hm
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let T := boundaryPlaneReflection ⁻¹' U
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hT : MeasurableSet T := hU.preimage boundaryPlaneReflection.continuous.measurable
  have he (z : LoopPlane) : z ∈ T ↔ z ∈ ball (0 : LoopPlane) R ∧ z 1 < 0 := by
    simp only [T, U, mem_preimage, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq,
      LinearIsometryEquiv.norm_map, (reflection_coordinates _).2, neg_pos]
  have hdis : Disjoint U T := by
    rw [Set.disjoint_left]
    exact fun z hu ht => (not_lt_of_ge hu.2.le) (he z |>.mp ht).2
  have hball : (U ∪ T : Set LoopPlane) =ᵐ[volume] ball (0 : LoopPlane) R := by
    have hz : ∀ᵐ z : LoopPlane ∂volume, z 1 ≠ 0 := by simpa only [ae_iff, not_not] using hnull
    filter_upwards [hz] with z hz
    apply propext
    change (z ∈ U ∨ z ∈ T) ↔ z ∈ ball (0 : LoopPlane) R
    constructor
    · exact fun h => h.elim And.left (fun ht => (he z |>.mp ht).1)
    · intro hb
      rcases lt_or_gt_of_ne hz with h | h
      · exact Or.inr (he z |>.mpr ⟨hb, h⟩)
      · exact Or.inl ⟨hb, h⟩
  rw [← setIntegral_congr_set hball, setIntegral_union hdis hT
    (hf.mono_set inter_subset_left) (hf.mono_set (fun z hz => (he z |>.mp hz).1))]
  congr 1
  have hc := boundaryPlaneReflection.measurePreserving.setIntegral_preimage_emb
    boundaryPlaneReflection.toHomeomorph.measurableEmbedding
    (fun z => f (boundaryPlaneReflection z)) U
  simpa only [Function.comp_def, reflection_involution] using hc

private theorem odd_holder {N : ℕ} {R beta H : ℝ} (hb : 0 < beta) (hH : 0 ≤ H)
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hh : ∀ x ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ∀ y ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ‖u y - u x‖ ≤ H * dist y x ^ beta)
    (hz : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}, z 1 = 0 → u z = 0) :
    let q := fun z => if 0 ≤ z 1 then u z else -u (boundaryPlaneReflection z)
    ContinuousOn q (closedBall (0 : LoopPlane) R) ∧
      ∀ x ∈ closedBall (0 : LoopPlane) R, ∀ y ∈ closedBall (0 : LoopPlane) R,
        ‖q y - q x‖ ≤ (2 * H) * dist y x ^ beta := by
  classical
  dsimp only []
  let q := fun z => if 0 ≤ z 1 then u z else -u (boundaryPlaneReflection z)
  have hup (z : LoopPlane) (hz : z ∈ closedBall (0 : LoopPlane) R) (hs : z 1 < 0) :
      boundaryPlaneReflection z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} := by
    exact ⟨by simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hz,
      by change 0 ≤ (boundaryPlaneReflection z) 1
         rw [(reflection_coordinates _).2]; linarith⟩
  have hc (x y : LoopPlane) (hx : x ∈ closedBall (0 : LoopPlane) R)
      (hy : y ∈ closedBall (0 : LoopPlane) R) (hxp : 0 ≤ x 1) (hyn : y 1 < 0) :
      ‖q y - q x‖ ≤ (2 * H) * dist y x ^ beta := by
    have hd : |y 1 - x 1| ≤ dist y x := by
      simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
        PiLp.norm_apply_le (y - x) 1
    have hxD : x 1 ≤ dist y x := by linarith [le_abs_self (x 1 - y 1), abs_sub_comm (x 1) (y 1)]
    have hyD : -y 1 ≤ dist y x := by linarith [le_abs_self (x 1 - y 1), abs_sub_comm (x 1) (y 1)]
    have hux := (odd_height_bound u hh hz x ⟨hx, hxp⟩).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp hxD hb.le) hH)
    have huy := odd_height_bound u hh hz _ (hup y hy hyn)
    rw [(reflection_coordinates _).2] at huy
    have huy' := huy.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hyD hb.le) hH)
    dsimp only [q]
    rw [if_pos hxp, if_neg (not_le.mpr hyn)]
    exact (norm_sub_le _ _).trans (by rw [norm_neg]; linarith)
  have hholder (x : LoopPlane) (hx : x ∈ closedBall (0 : LoopPlane) R)
      (y : LoopPlane) (hy : y ∈ closedBall (0 : LoopPlane) R) :
      ‖q y - q x‖ ≤ (2 * H) * dist y x ^ beta := by
    have hdouble : H * dist y x ^ beta ≤ (2 * H) * dist y x ^ beta := by
      nlinarith [Real.rpow_nonneg (dist_nonneg : 0 ≤ dist y x) beta]
    by_cases hxp : 0 ≤ x 1 <;> by_cases hyp : 0 ≤ y 1
    · simpa only [q, if_pos hxp, if_pos hyp] using (hh x ⟨hx, hxp⟩ y ⟨hy, hyp⟩).trans hdouble
    · exact hc x y hx hy hxp (lt_of_not_ge hyp)
    · simpa only [norm_sub_rev, dist_comm] using hc y x hy hx hyp (lt_of_not_ge hxp)
    · have hu := hh _ (hup x hx (lt_of_not_ge hxp)) _ (hup y hy (lt_of_not_ge hyp))
      rw [boundaryPlaneReflection.dist_map] at hu
      simpa only [q, if_neg hxp, if_neg hyp, neg_sub_neg, norm_sub_rev] using hu.trans hdouble
  refine ⟨?_, hholder⟩
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd : Tendsto (fun z : LoopPlane => dist z x)
      (𝓝[closedBall (0 : LoopPlane) R] x) (𝓝 0) := by
    have hc : Continuous (fun z : LoopPlane => dist z x) := continuous_id.dist continuous_const
    simpa only [dist_self] using (hc.tendsto x).mono_left nhdsWithin_le_nhds
  have ht := (hd.rpow_const_nhds_zero hb).const_mul (2 * H)
  rw [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [dist_eq_norm] using hholder x hx y hy

set_option maxHeartbeats 1600000 in

theorem halfDisk_odd_localMap {N : ℕ} {R beta H : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (u : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hAE : u =ᵐ[volume.restrict (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})] X.value)
    (hu : MemLp u 2 (volume.restrict
      (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1})))
    (hd : ∀ i, MemLp (X.derivative i) 2 (volume.restrict
      (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1})))
    (hb : 0 < beta) (hH : 0 ≤ H)
    (_huc : ContinuousOn u (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hh : ∀ x ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ∀ y ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1},
      ‖u y - u x‖ ≤ H * dist y x ^ beta)
    (hz : ∀ z ∈ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}, z 1 = 0 → u z = 0) :
    ∃ Y : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
        (ball (0 : LoopPlane) R),
      (∀ z, Y.value z = if 0 ≤ z 1 then u z else -u (boundaryPlaneReflection z)) ∧
      (∀ i z, Y.derivative i z = if 0 ≤ z 1 then X.derivative i z else
        (if i = 0 then (-1 : ℝ) else 1) • X.derivative i (boundaryPlaneReflection z)) ∧
      ContinuousOn Y.value (closedBall (0 : LoopPlane) R) ∧
      ∀ x ∈ closedBall (0 : LoopPlane) R, ∀ y ∈ closedBall (0 : LoopPlane) R,
        ‖Y.value y - Y.value x‖ ≤ (2 * H) * dist y x ^ beta := by
  classical
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let B := ball (0 : LoopPlane) R
  let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  let A : Set LoopPlane := {z | 0 ≤ z 1}
  let q := fun z => if 0 ≤ z 1 then u z else -u (boundaryPlaneReflection z)
  let sig := fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1
  let d := fun i z => if 0 ≤ z 1 then X.derivative i z else
    (if i = 0 then (-1 : ℝ) else 1) • X.derivative i (boundaryPlaneReflection z)
  let basis := EuclideanSpace.basisFun (Fin 2) ℝ
  have hA : MeasurableSet A :=
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hU : MeasurableSet U := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hUS : U ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hq : MemLp q 2 (volume.restrict (closedBall (0 : LoopPlane) R)) := by
    have he := halfDisk_even_memLp hu
    apply (MemLp.piecewise hA (he.restrict A) (he.neg.restrict Aᶜ)).ae_eq
    exact ae_of_all _ fun z => by by_cases h : 0 ≤ z 1 <;> simp [q, A, h]
  have hD (i : Fin 2) : MemLp (d i) 2 (volume.restrict (closedBall (0 : LoopPlane) R)) := by
    have he := halfDisk_even_memLp (hd i)
    apply (MemLp.piecewise hA (he.restrict A)
      ((he.const_smul (if i = 0 then (-1 : ℝ) else 1)).restrict Aᶜ)).ae_eq
    exact ae_of_all _ fun z => by
      fin_cases i <;> by_cases h : 0 ≤ z 1 <;> simp [d, A, h]
  have hhalf (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
      (hs : tsupport test ⊆ B) (i : Fin 2) (j : Fin N) :
      (∫ z in U, test z * X.derivative i z j) =
        -(∫ z in U, fderiv ℝ test z (basis i) * u z j) := by
    apply odd_half_weak hR hb hH (fun z => u z j) (fun z => X.derivative i z j) i
      ((hu.mono_measure (Measure.restrict_mono_set volume hUS)).eval_piLp j)
      (((hd i).mono_measure (Measure.restrict_mono_set volume hUS)).eval_piLp j)
    · exact fun z hz' => (PiLp.norm_apply_le (u z) j).trans
        (odd_height_bound u hh hz z (hUS hz'))
    · intro t ht hts
      rw [X.weak_derivative t ht hts]
      congr 1
      exact integral_congr_ae (hAE.mono (fun z he => by dsimp only []; rw [he]; rfl))
    · exact hc
    · exact hs
  have hweak (test : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport test)
      (hs : tsupport test ⊆ B) (i : Fin 2) (j : Fin N) :
      (∫ z in B, test z * d i z j) = -(∫ z in B, fderiv ℝ test z (basis i) * q z j) := by
    let psi : 𝓢(LoopPlane, ℝ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      boundaryPlaneReflection.toContinuousLinearEquiv test
    have hpsi (z : LoopPlane) : psi z = test (boundaryPlaneReflection z) := rfl
    have hpc : HasCompactSupport psi :=
      hc.comp_isClosedEmbedding boundaryPlaneReflection.toHomeomorph.isClosedEmbedding
    have hps : tsupport psi ⊆ B := by
      have he := tsupport_comp_eq_preimage (test : LoopPlane → ℝ)
        boundaryPlaneReflection.toHomeomorph
      change tsupport ((test : LoopPlane → ℝ) ∘ boundaryPlaneReflection.toHomeomorph) ⊆ B
      rw [he]
      intro z hz'
      have hm : boundaryPlaneReflection z ∈ B := hs hz'
      simpa only [B, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hm
    have hpsid (z : LoopPlane) : fderiv ℝ psi z (basis i) =
        sig i * fderiv ℝ test (boundaryPlaneReflection z) (basis i) := by
      have he := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (basis i))
        ((test.differentiableAt.hasFDerivAt.comp z
          boundaryPlaneReflection.toContinuousLinearEquiv.hasFDerivAt).fderiv)
      change fderiv ℝ psi z (basis i) =
        fderiv ℝ test (boundaryPlaneReflection z) (boundaryPlaneReflection (basis i)) at he
      rw [show boundaryPlaneReflection (basis i) = sig i • basis i by
        ext k; fin_cases i <;> fin_cases k <;>
          simp [basis, sig, boundaryPlaneReflection, Complex.orthonormalBasisOneI_repr_apply,
            EuclideanSpace.basisFun_apply], map_smul, smul_eq_mul] at he
      exact he
    have hl : IntegrableOn (fun z => test z * d i z j) B :=
      (test.memLp 2 volume).restrict B |>.integrable_mul
      (((hD i).mono_measure (Measure.restrict_mono_set volume ball_subset_closedBall)).eval_piLp j)
    have hr : IntegrableOn (fun z => fderiv ℝ test z (basis i) * q z j) B :=
      ((∂_{basis i} test).memLp 2 volume).restrict B |>.integrable_mul
        ((hq.mono_measure (Measure.restrict_mono_set volume ball_subset_closedBall)).eval_piLp j)
    rw [odd_integral_split hl, odd_integral_split hr]
    have hUL : (∫ z in U, test z * d i z j) = ∫ z in U, test z * X.derivative i z j := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU] with z hz'
      simp only [d, if_pos (show 0 < z 1 from hz'.2).le]
    have hUR : (∫ z in U, fderiv ℝ test z (basis i) * q z j) =
        ∫ z in U, fderiv ℝ test z (basis i) * u z j := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU] with z hz'
      simp only [q, if_pos (show 0 < z 1 from hz'.2).le]
    have hLL : (∫ z in U, test (boundaryPlaneReflection z) * d i (boundaryPlaneReflection z) j) =
        -(sig i) * ∫ z in U, psi z * X.derivative i z j := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU] with z hz'
      have hn : ¬0 ≤ (boundaryPlaneReflection z) 1 := by
        rw [(reflection_coordinates _).2]; linarith [show 0 < z 1 from hz'.2]
      simp only [d, if_neg hn, reflection_involution, PiLp.smul_apply, smul_eq_mul, hpsi]
      by_cases hi : i = 0 <;> simp [sig, hi]
    have hLR : (∫ z in U,
        fderiv ℝ test (boundaryPlaneReflection z) (basis i) * q (boundaryPlaneReflection z) j) =
        -(sig i) * ∫ z in U, fderiv ℝ psi z (basis i) * u z j := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU] with z hz'
      have hn : ¬0 ≤ (boundaryPlaneReflection z) 1 := by
        rw [(reflection_coordinates _).2]; linarith [show 0 < z 1 from hz'.2]
      simp only [q, if_neg hn, reflection_involution, PiLp.neg_apply, hpsid]
      by_cases hi : i = 0 <;> simp [sig, hi]
    rw [hUL, hLL, hUR, hLR, hhalf test hc hs i j, hhalf psi hpc hps i j]
    ring
  refine ⟨⟨q, d, ?_, ?_, fun t ht hs i j => hweak t ht hs i j⟩,
    fun _ => rfl, fun _ _ => rfl, ?_⟩
  · intro K _ hK
    exact hq.mono_measure (Measure.restrict_mono_set volume (hK.trans ball_subset_closedBall))
  · intro i K _ hK
    exact (hD i).mono_measure (Measure.restrict_mono_set volume (hK.trans ball_subset_closedBall))
  · exact odd_holder hb hH u hh hz

end PoincareConjecture.M65Boundary
