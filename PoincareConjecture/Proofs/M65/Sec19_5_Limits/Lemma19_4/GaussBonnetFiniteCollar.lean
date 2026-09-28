import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCollarRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Manifold BigOperators

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace

private theorem translated_subdivision_integral {N : ℕ} (v : ℕ → ℝ)
    (tag : Fin N → ℝ) (f : ℝ → ℝ)
    (hf : ∀ k < N, IntervalIntegrable f volume (v k) (v (k + 1))) :
    (∑ i : Fin N, ∫ t in (v i - tag i)..(v (i.val + 1) - tag i), f (t + tag i)) =
      ∫ t in v 0..v N, f t := by
  simp_rw [intervalIntegral.integral_comp_add_right, sub_add_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ t in v k..v (k + 1), f t) N]
  exact intervalIntegral.sum_integral_adjacent_intervals hf

private theorem connection_continuousOn
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H T N : ℂ → LoopAmbient} {U : Set ℂ} (hU : IsOpen U)
    (hH : ContDiffOn ℝ 1 H U) (hT : ContDiffOn ℝ 1 T U)
    (hN : ContinuousOn N U) :
    ContinuousOn (fun z => g.inner (H z)
      (covariantDerivativeAlongMap D H T z 1) (N z)) U := by
  have hG : ContinuousOn (fun z => g.euclideanCoefficients (H z)) U :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous.comp_continuousOn
      hH.continuousOn
  have hDH : ContinuousOn (fun z => fderiv ℝ H z 1) U :=
    ((hH.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply continuousOn_const
  have hDT : ContinuousOn (fun z => fderiv ℝ T z 1) U :=
    ((hT.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply continuousOn_const
  have hGamma : ContinuousOn (fun z => connectionCoefficient D (H z)) U :=
    (contDiff_connectionCoefficient D).continuous.comp_continuousOn hH.continuousOn
  exact (hG.clm_apply (hDT.add ((hGamma.clm_apply hDH).clm_apply hT.continuousOn))).clm_apply hN

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

set_option maxHeartbeats 2000000 in

theorem exists_boundary_radial_lower_limit (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ∀ s, W (periodicFreeLoop gamma s) = M65Filling.loopCurvature connection gamma s) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
      (W (S.disk.map (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
    let L := fun (h theta : ℝ) =>
      let z := e.symm (Real.exp (-h) • Proofs.M58.angularPoint theta)
      fderiv ℝ (fun w => Real.log (S.conformalFactor (e w))) z z / 2
    IntervalIntegrable B volume (-Real.pi) Real.pi ∧
      ∃ (h A : ℕ → ℝ), (∀ k, 0 < h k) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto A atTop (𝓝 (2 * Real.pi + ∫ theta in (-Real.pi)..Real.pi, B theta)) ∧
        ∀ k, IntervalIntegrable (L (h k)) volume (-Real.pi) Real.pi ∧
          A k ≤ -(∫ theta in (-Real.pi)..Real.pi, L (h k) theta) := by
  classical
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
    (W (S.disk.map (Proofs.M58.angularPoint theta)))
    (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
      (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
  let L := fun (h theta : ℝ) =>
    let z := e.symm (Real.exp (-h) • Proofs.M58.angularPoint theta)
    fderiv ℝ (fun w => Real.log (S.conformalFactor (e w))) z z / 2
  have hB : Continuous B := S.boundary_curvature_flux_continuous hinj hsmooth hregular W hW
  choose gE DE r d C F hr hd hdr hC hH hF hF1 hDF hholder hradial hboundary using
    fun a : ℝ => S.exists_angular_collar hinj hsmooth hregular W hW a
  let P := fun a => e ∘ boundaryCoordinate (e.symm (Proofs.M58.angularPoint a))
  let H := fun a => (chartAt LoopAmbient (S.disk.map (Proofs.M58.angularPoint a))) ∘
    S.disk.map ∘ P a
  let K := fun a => closedBall (0 : ℂ) (r a) ∩ {z | 0 ≤ z.im}
  let U := fun a => ball (0 : ℂ) (r a) ∩ {z | 0 < z.im}
  have hU (a : ℝ) : IsOpen (U a) :=
    isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUK (a : ℝ) : U a ⊆ K a := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  let V := fun a => Ioo (a - d a) (a + d a)
  have hcover : Icc (-Real.pi) Real.pi ⊆ ⋃ a, V a := by
    intro t _ht
    exact mem_iUnion.mpr ⟨t, by exact ⟨sub_lt_self _ (hd t), lt_add_of_pos_right _ (hd t)⟩⟩
  obtain ⟨N, hN, tag, htag⟩ := exists_subordinate_uniform_subdivision
    (neg_lt_self Real.pi_pos) V (fun _ => isOpen_Ioo) hcover
  let v := fun k : ℕ => -Real.pi + (Real.pi - (-Real.pi)) * (k : ℝ) / N
  let a := fun i : Fin N => v i - tag i
  let b := fun i : Fin N => v (i.val + 1) - tag i
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hv0 : v 0 = -Real.pi := by simp only [v, Nat.cast_zero, mul_zero, zero_div, add_zero]
  have hvN : v N = Real.pi := by
    dsimp only [v]
    rw [mul_div_cancel_right₀ _ hNR.ne']
    ring
  have hvmono (k : ℕ) : v k ≤ v (k + 1) := by
    dsimp only [v]
    push_cast
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) (by linarith [Real.pi_pos])) hNR.le
  have hab (i : Fin N) : a i ≤ b i := sub_le_sub_right (hvmono i) _
  have hcell (i : Fin N) : Icc (v i) (v (i.val + 1)) ⊆ V (tag i) := by
    simpa only [v, Nat.cast_add, Nat.cast_one] using htag i
  have hlocal (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      t ∈ Icc (-d (tag i)) (d (tag i)) := by
    have hh := hcell i (show t + tag i ∈ Icc (v i) (v (i.val + 1)) by
      change v i - tag i ≤ t ∧ t ≤ v (i.val + 1) - tag i at ht
      constructor <;> linarith [ht.1, ht.2])
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  obtain ⟨R0, hR0, hR01, hpositive⟩ := S.exists_regular_annulus
  have hnear : ∀ᶠ h : ℝ in 𝓝 0,
      (∀ i : Fin N, h < d (tag i)) ∧ R0 < Real.exp (-h) := by
    have hfirst : ∀ i : Fin N, ∀ᶠ h : ℝ in 𝓝 0, h < d (tag i) :=
      fun i => gt_mem_nhds (hd (tag i))
    have hlast : ∀ᶠ h : ℝ in 𝓝 0, R0 < Real.exp (-h) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt.eventually
        (lt_mem_nhds (by simpa only [Function.comp_apply, neg_zero, Real.exp_zero] using hR01))
    exact (Filter.eventually_all.mpr hfirst).and hlast
  obtain ⟨eta, heta, hetasub⟩ := Metric.mem_nhds_iff.mp hnear
  let delta := eta / 2
  have hdelta : 0 < delta := half_pos heta
  have hdeltaeta : delta < eta := by dsimp only [delta]; linarith
  have hsmall (h : ℝ) (hh : h ∈ Icc (0 : ℝ) delta) :
      (∀ i : Fin N, h < d (tag i)) ∧ R0 < Real.exp (-h) := by
    apply hetasub
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2.trans_lt hdeltaeta
  have hrect (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (h : ℝ) (hh : h ∈ Icc (0 : ℝ) delta) :
      (t : ℂ) + (h : ℂ) * I ∈ K (tag i) := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, by simpa using hh.1⟩
    have htbound := abs_le.mpr (hlocal i t ht)
    have hhbound := (hsmall h hh).1 i
    calc
      ‖(t : ℂ) + (h : ℂ) * I‖ ≤ ‖(t : ℂ)‖ + ‖(h : ℂ) * I‖ := norm_add_le _ _
      _ = |t| + h := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh.1]
      _ ≤ r (tag i) := by linarith [hdr (tag i), hr (tag i)]
  have hrectU (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) delta) :
      (t : ℂ) + (h : ℂ) * I ∈ U (tag i) := by
    refine ⟨mem_ball_zero_iff.mpr ?_, by simpa using hh.1⟩
    have htbound := abs_le.mpr (hlocal i t ht)
    have hhbound := (hsmall h ⟨hh.1.le, hh.2.le⟩).1 i
    calc
      ‖(t : ℂ) + (h : ℂ) * I‖ ≤ ‖(t : ℂ)‖ + ‖(h : ℂ) * I‖ := norm_add_le _ _
      _ = |t| + h := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh.1]
      _ < r (tag i) := by linarith [hdr (tag i), hr (tag i)]
  let T := fun a z => (F a z).1
  let NN := fun a z => (F a z).2
  have hDN (s : ℝ) : MemLp (fun z => fderiv ℝ (NN s) z 1)
      2 (volume.restrict (K s ∩ U s)) := by
    rw [inter_eq_right.mpr (hUK s)]
    apply (hDF s).snd.ae_eq
    filter_upwards [ae_restrict_mem (hU s).measurableSet] with z hz
    have hfz := ((hF1 s).contDiffAt ((hU s).mem_nhds hz)).differentiableAt one_ne_zero
    exact (congrArg (fun L : ℂ →L[ℝ] LoopAmbient => L 1) hfz.hasFDerivAt.snd.fderiv).symm
  obtain ⟨h, hh, hlim, hconnection⟩ := finite_weighted_connection_collar_limit
    (fun i : Fin N => gE (tag i)) (fun i => DE (tag i))
    (fun i => H (tag i)) (fun i => T (tag i)) (fun i => NN (tag i))
    (fun _ _ => (1 : ℝ))
    (fun i => (isCompact_closedBall (0 : ℂ) (r (tag i))).inter_right
      (isClosed_le continuous_const continuous_im))
    (fun i => (halfDisk_differential_domain (hr (tag i))).2.2.1)
    (fun i => hU (tag i)) (fun i => hUK (tag i)) (fun i => hH (tag i))
    (fun _ => contDiffOn_const) (fun i => (hF (tag i)).fst)
    (fun i => (hF1 (tag i)).fst) (fun i => (hF (tag i)).snd)
    (fun i => (hF1 (tag i)).snd) (fun i => hDN (tag i))
    a b (fun i => C (tag i)) hdelta hab (fun i => hC (tag i)) hrect hrectU
    (fun i t ht => (hboundary (tag i) t (hlocal i t ht)).1)
    (fun i z hz y hy => (norm_fst_le (F (tag i) z - F (tag i) y)).trans
      (hholder (tag i) z hz y hy))
  let J := fun (i : Fin N) (h : ℝ) (t : ℝ) =>
    let z := (t : ℂ) + (h : ℂ) * I
    (gE (tag i)).inner (H (tag i) z)
      (covariantDerivativeAlongMap (DE (tag i)) (H (tag i)) (T (tag i)) z 1)
      (NN (tag i) z)
  let A := fun k => 2 * Real.pi - ∑ i : Fin N, ∫ t in (a i)..(b i), J i (h k) t
  have hLC (k : ℕ) : Continuous (L (h k)) :=
    S.radial_log_flux_continuous (Real.exp_pos _)
      (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (hh k).1))
      (fun z hz => hpositive z (by
        rw [hz]
        exact (hsmall (h k) ⟨(hh k).1.le, (hh k).2.le⟩).2) (by
        rw [hz]
        exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (hh k).1)))
  have hJC (i : Fin N) (k : ℕ) : ContinuousOn (J i (h k)) (Icc (a i) (b i)) :=
    (connection_continuousOn (DE (tag i)) (hU (tag i))
      ((hH (tag i)).mono (hUK (tag i))) (hF1 (tag i)).fst
      ((hF (tag i)).snd.mono (hUK (tag i)))).comp
        (continuous_ofReal.add continuous_const).continuousOn (fun t ht => hrectU i t ht _ (hh k))
  have hJlim (i : Fin N) : Tendsto (fun k => ∫ t in (a i)..(b i), J i (h k) t)
      atTop (𝓝 (-(∫ t in (a i)..(b i), B (t + tag i)))) := by
    have heq : (∫ t in (a i)..(b i), (gE (tag i)).inner (H (tag i) (t : ℂ))
        (deriv (fun s : ℝ => T (tag i) (s : ℂ)) t +
          connectionCoefficient (DE (tag i)) (H (tag i) (t : ℂ))
            (fderivWithin ℝ (H (tag i)) (K (tag i)) (t : ℂ) 1)
            (T (tag i) (t : ℂ))) (NN (tag i) (t : ℂ))) =
        -(∫ t in (a i)..(b i), B (t + tag i)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hboundary (tag i) t (hlocal i t (by
        simpa only [uIcc_of_le (hab i)] using ht))).2
    have hh' := hconnection i
    simp only [one_mul] at hh'
    rw [heq] at hh'
    exact hh'
  have hsumB : (∑ i : Fin N, ∫ t in (a i)..(b i), B (t + tag i)) =
      ∫ t in (-Real.pi)..Real.pi, B t := by
    simpa only [a, b, hv0, hvN] using translated_subdivision_integral v tag B
      (fun _ _ => hB.intervalIntegrable _ _)
  have hwidth : (∑ i : Fin N, (b i - a i)) = 2 * Real.pi := by
    have hc := translated_subdivision_integral v tag (fun _ => (1 : ℝ))
      (fun _ _ => intervalIntegrable_const)
    have hc' : (∑ i : Fin N, (b i - a i)) = Real.pi - (-Real.pi) := by
      simpa only [a, b, intervalIntegral.integral_const, smul_eq_mul, mul_one,
        hv0, hvN] using hc
    exact hc'.trans (by ring)
  have hAlim : Tendsto A atTop
      (𝓝 (2 * Real.pi + ∫ t in (-Real.pi)..Real.pi, B t)) := by
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hJlim i)
    have ha := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * Real.pi)
      atTop (𝓝 (2 * Real.pi))).sub hs
    simpa only [Finset.sum_neg_distrib, hsumB, sub_neg_eq_add, A] using ha
  refine ⟨hB.intervalIntegrable _ _, h, A, fun k => (hh k).1, hlim, hAlim, ?_⟩
  intro k
  refine ⟨(hLC k).intervalIntegrable _ _, ?_⟩
  have hle (i : Fin N) : (∫ t in (a i)..(b i), L (h k) (t + tag i)) ≤
      (∫ t in (a i)..(b i), J i (h k) t) - (b i - a i) := by
    have hi := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun t => L (h k) (t + tag i)) (g := fun t => J i (h k) t - 1) (hab i)
      (((hLC k).comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
      (((hJC i k).sub continuousOn_const).intervalIntegrable_of_Icc (hab i))
      (fun t ht => ?_)
    · simpa only [intervalIntegral.integral_sub
        ((hJC i k).intervalIntegrable_of_Icc (hab i)) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_one] using hi
    · have hp := boundaryCoordinate_angular_radius (tag i) t (h k)
      have he : boundaryCoordinate (e.symm (Proofs.M58.angularPoint (tag i)))
          ((t : ℂ) + (h k : ℂ) * I) =
          e.symm (Real.exp (-h k) • Proofs.M58.angularPoint (t + tag i)) := by
        exact (e.symm_apply_apply _).symm.trans (congrArg e.symm hp)
      have hi := hradial (tag i) ((t : ℂ) + (h k : ℂ) * I) (hrectU i t ht _ (hh k))
      change fderiv ℝ (fun w => Real.log (S.conformalFactor (e w)))
          (boundaryCoordinate (e.symm (Proofs.M58.angularPoint (tag i)))
            ((t : ℂ) + (h k : ℂ) * I))
          (boundaryCoordinate (e.symm (Proofs.M58.angularPoint (tag i)))
            ((t : ℂ) + (h k : ℂ) * I)) / 2 ≤ J i (h k) t - 1 at hi
      rw [he] at hi
      exact hi
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
  have hsumL : (∑ i : Fin N, ∫ t in (a i)..(b i), L (h k) (t + tag i)) =
      ∫ t in (-Real.pi)..Real.pi, L (h k) t := by
    simpa only [a, b, hv0, hvN] using translated_subdivision_integral v tag (L (h k))
      (fun _ _ => (hLC k).intervalIntegrable _ _)
  rw [hsumL, Finset.sum_sub_distrib, hwidth] at hsum
  dsimp only [A]
  linarith

end PoincareConjecture.M65MinimalDisk
