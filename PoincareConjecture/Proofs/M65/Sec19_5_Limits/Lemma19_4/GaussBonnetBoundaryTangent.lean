import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace

private theorem metric_normalize_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) (v : E) :
    (Real.sqrt (G (a • v) (a • v)))⁻¹ • (a • v) =
      (a / |a|) • ((Real.sqrt (G v v))⁻¹ • v) := by
  have hs : Real.sqrt (G (a • v) (a • v)) = |a| * Real.sqrt (G v v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show a * (a * G v v) = a ^ 2 * G v v by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
  rw [hs, smul_smul, smul_smul]
  congr 1
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

theorem regular_curve_unit_tangent_contDiffAt {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {f : ℝ → ℝ} {t : ℝ}
    (hc : ContDiffAt ℝ 2 c (f t)) (hv : deriv c (f t) ≠ 0)
    (hf : ContDiffAt ℝ 1 f t) :
    ContDiffAt ℝ 1 (fun s =>
      (Real.sqrt (g.inner (c (f s)) (deriv c (f s)) (deriv c (f s))))⁻¹ •
        deriv c (f s)) t := by
  have hV : ContDiffAt ℝ 1 (fun s => deriv c (f s)) t :=
    ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).comp t hf
  have hcf : ContDiffAt ℝ 1 (fun s => c (f s)) t :=
    (hc.of_le (by norm_num)).comp t hf
  have hG : ContDiffAt ℝ 1 (fun s => g.euclideanCoefficients (c (f s))) t :=
    ((g.contDiffAt_euclideanCoefficients _).of_le (by simp)).comp t hcf
  have hpos : 0 < g.inner (c (f t)) (deriv c (f t)) (deriv c (f t)) :=
    g.pos _ _ hv
  exact ((((hG.clm_apply hV).clm_apply hV).sqrt hpos.ne').inv
    (Real.sqrt_pos.mpr hpos).ne').smul hV

theorem halfDisk_boundary_tangent {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : Even m)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hF : ContinuousOn
      (fun z => normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z))
      (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := (normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z)).1
      g.inner (H z) T T = 1)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {f : ℝ → ℝ}
    (hc : ContDiffAt ℝ 2 c (f 0)) (hc0 : deriv c (f 0) ≠ 0)
    (hf : ContDiff ℝ 1 f) (hmono : Monotone f ∨ Antitone f)
    (hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (f t)) :
    let T := fun t : ℝ =>
      (normalizedResidualFrame (g.euclideanCoefficients (H (t : ℂ))) (Q (t : ℂ))).1
    let U := fun t : ℝ =>
      (Real.sqrt (g.inner (c (f t)) (deriv c (f t)) (deriv c (f t))))⁻¹ • deriv c (f t)
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), T t = ε • U t) ∧ ContDiffAt ℝ 1 T 0 := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let A := fun t : ℝ => residualRealColumn (Q (t : ℂ))
  let T := fun t : ℝ =>
    (normalizedResidualFrame (g.euclideanCoefficients (H (t : ℂ))) (Q (t : ℂ))).1
  let U := fun t : ℝ =>
    (Real.sqrt (g.inner (c (f t)) (deriv c (f t)) (deriv c (f t))))⁻¹ • deriv c (f t)
  have hTc : ContinuousAt T 0 := by
    have hreal : ContinuousOn T (Ioo (-r) r) :=
      hF.fst.comp continuous_ofReal.continuousOn (fun t ht => by
        refine ⟨mem_closedBall_zero_iff.mpr ?_, by simp⟩
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_lt.mpr ⟨ht.1, ht.2⟩).le)
    exact hreal.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩)
  have hU : ContDiffAt ℝ 1 U 0 :=
    regular_curve_unit_tangent_contDiffAt g hc hc0 hf.contDiffAt
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < r :=
    continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
  have hcd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ c (f t) :=
    hf.continuous.continuousAt.eventually ((hc.eventually (by norm_num)).mono
      (fun _ ht => ht.differentiableAt (by norm_num)))
  have hraw : ∀ᶠ t in 𝓝 (0 : ℝ), t ≠ 0 →
      deriv f t ≠ 0 ∧ (deriv f t / |deriv f t|) • U t = T t := by
    filter_upwards [hnear, hcd, hcurve.eventually_nhds] with t ht hct hcurvet htn
    have hK : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr ht.le, by simp⟩
    have hD := hct.hasDerivAt.scomp t (hf.differentiable one_ne_zero t).hasDerivAt
    have hce : (fun s : ℝ => H (s : ℂ)) =ᶠ[𝓝 t] c ∘ f := hcurvet
    have hdiam := (halfDisk_hasDerivAt_diameter hH ht).congr_of_eventuallyEq hce.symm
    have hactual := hD.unique hdiam
    let L := fderivWithin ℝ H K (t : ℂ)
    have hreal : residualRealColumn (halfDiskGradient H r (t : ℂ)) = L 1 := by
      simpa only [complexGradient, L.fderiv, L, halfDiskGradient, K] using
        (residual_columns_complexGradient L 0).1
    rw [hfactor (t : ℂ) hK, (residual_columns_smul _ _).1] at hreal
    simp only [← Complex.ofReal_pow, ofReal_re, ofReal_im, zero_smul, add_zero] at hreal
    have hfac : deriv f t • deriv c (f t) = t ^ m • A t := hactual.trans hreal.symm
    have hA : A t ≠ 0 := by
      intro hz
      have hh := hunit (t : ℂ) hK
      change g.inner (H (t : ℂ))
        ((Real.sqrt (g.inner (H (t : ℂ)) (A t) (A t)))⁻¹ • A t)
        ((Real.sqrt (g.inner (H (t : ℂ)) (A t) (A t)))⁻¹ • A t) = 1 at hh
      simp only [hz, smul_zero, map_zero] at hh
      exact zero_ne_one hh
    have hb : 0 < t ^ m := hm.pow_pos htn
    have hd : deriv f t ≠ 0 := by
      intro hd
      rw [hd, zero_smul] at hfac
      exact (smul_ne_zero hb.ne' hA) hfac.symm
    refine ⟨hd, ?_⟩
    have hnorm := congrArg (fun v =>
      (Real.sqrt (g.inner (H (t : ℂ)) v v))⁻¹ • v) hfac
    change (Real.sqrt (g.euclideanCoefficients (H (t : ℂ))
      (deriv f t • deriv c (f t)) (deriv f t • deriv c (f t))))⁻¹ •
        (deriv f t • deriv c (f t)) =
      (Real.sqrt (g.euclideanCoefficients (H (t : ℂ))
        (t ^ m • A t) (t ^ m • A t)))⁻¹ • (t ^ m • A t) at hnorm
    rw [metric_normalize_smul, metric_normalize_smul,
      abs_of_pos hb, div_self hb.ne', one_smul] at hnorm
    change (deriv f t / |deriv f t|) •
      ((Real.sqrt (g.inner (H (t : ℂ)) (deriv c (f t)) (deriv c (f t))))⁻¹ •
        deriv c (f t)) = T t at hnorm
    have hvalue : H (t : ℂ) = c (f t) := hce.self_of_nhds
    dsimp only [U]
    rw [← hvalue]
    exact hnorm
  obtain ⟨ε, hε, hsign⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ t, deriv f t ≠ 0 → deriv f t / |deriv f t| = ε := by
    rcases hmono with hm | hm
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro t ht
      rw [abs_of_pos (lt_of_le_of_ne hm.deriv_nonneg (Ne.symm ht)), div_self ht]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro t ht
      rw [abs_of_neg (lt_of_le_of_ne hm.deriv_nonpos ht), div_neg, div_self ht]
  have hpunc : T =ᶠ[𝓝[≠] (0 : ℝ)] fun t => ε • U t := by
    filter_upwards [hraw.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htn
    obtain ⟨hd, he⟩ := ht htn
    rw [hsign t hd] at he
    exact he.symm
  have hεU : ContinuousAt (fun t => ε • U t) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => ε) 0).smul hU.continuousAt
  have hzero : T 0 = ε • U 0 := tendsto_nhds_unique_of_eventuallyEq
    (hTc.tendsto.mono_left nhdsWithin_le_nhds)
    (hεU.tendsto.mono_left nhdsWithin_le_nhds) hpunc
  have heq : T =ᶠ[𝓝 (0 : ℝ)] fun t => ε • U t := by
    filter_upwards [hraw] with t ht
    by_cases ht0 : t = 0
    · simpa only [ht0] using hzero
    · obtain ⟨hd, he⟩ := ht ht0
      rw [hsign t hd] at he
      exact he.symm
  have hεUd : ContDiffAt ℝ 1 (fun t => ε • U t) 0 :=
    (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => ε) 0).smul hU
  exact ⟨ε, hε, heq, hεUd.congr_of_eventuallyEq heq⟩

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_normalized_tangent_contDiffAt (S : M65MinimalDisk g connection gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1)
    (gE : RiemannianMetric 3 LoopAmbient) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hm : Even m) (Q : ℂ → Fin 3 → ℂ) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ boundaryCoordinate (e.symm x)
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
    ContDiffOn ℝ 1 H K →
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) →
      ContinuousOn F K →
      (∀ z ∈ K, gE.inner (H z) (F z).1 (F z).1 = 1) →
      ContDiffAt ℝ 1 (fun t : ℝ => (F (t : ℂ)).1) 0 := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let q := chartAt LoopAmbient (S.disk.map x)
  let P := e ∘ boundaryCoordinate p
  let H := q ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
  change ContDiffOn ℝ 1 H K →
    (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) → ContinuousOn F K →
    (∀ z ∈ K, gE.inner (H z) (F z).1 (F z).1 = 1) →
    ContDiffAt ℝ 1 (fun t : ℝ => (F (t : ℂ)).1) 0
  intro hH hfactor hF hunit
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  let a := Complex.arg p
  have hexp : Complex.exp ((a : ℂ) * I) = p := by
    simpa only [hp, ofReal_one, one_mul, a] using Complex.norm_mul_exp_arg_mul_I p
  have hangular (t : ℝ) : e.symm (Proofs.M58.angularPoint t) =
      Complex.exp ((t : ℂ) * I) := by
    rw [Complex.exp_ofReal_mul_I]
    rfl
  have hP (t : ℝ) : P (t : ℂ) = Proofs.M58.angularPoint (t + a) := by
    apply e.symm.injective
    change e.symm (e (boundaryCoordinate p (t : ℂ))) = _
    rw [e.symm_apply_apply, hangular, ofReal_add, add_mul, Complex.exp_add, hexp]
    simp only [boundaryCoordinate, mul_comm I (t : ℂ), mul_comm p]
  have hP0 : P (0 : ℂ) = x := by
    simp only [P, Function.comp_apply, boundaryCoordinate, mul_zero, Complex.exp_zero,
      mul_one, p, e.apply_symm_apply]
  have hax : Proofs.M58.angularPoint a = x := by
    simpa only [zero_add, ofReal_zero, hP0] using (hP 0).symm
  obtain ⟨h, hh, hlift, horient⟩ := M65Filling.boundary_lift S hsmooth hregular
  let f := fun t : ℝ => h (t + a)
  let c := q ∘ periodicFreeLoop gamma
  let J := periodicFreeLoop gamma ⁻¹' q.source
  have hf : ContDiff ℝ 1 f := hh.comp (contDiff_id.add contDiff_const)
  have hmono : Monotone f ∨ Antitone f := by
    rcases horient with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inl (fun s t hst => hm.monotone (show s + a ≤ t + a by linarith))
    · exact Or.inr (fun s t hst => hm.antitone (show s + a ≤ t + a by linarith))
  have hcenter : periodicFreeLoop gamma (f 0) = S.disk.map x := by
    simpa only [f, zero_add, hax] using (hlift a).symm
  have hsource : periodicFreeLoop gamma (f 0) ∈ q.source := by
    rw [hcenter]
    exact mem_chart_source LoopAmbient _
  have hJ : IsOpen J := q.open_source.preimage hsmooth.continuous
  have hc : ContDiffOn ℝ ∞ c J :=
    (contMDiffOn_chart.comp hsmooth.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hcAt : ContDiffAt ℝ 2 c (f 0) :=
    (hc.contDiffAt (hJ.mem_nhds hsource)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hqd := (mdifferentiable_chart (I := 𝓡 3) (S.disk.map x)).mdifferentiableAt hsource
  have hcd := (hsmooth (f 0)).mdifferentiableAt (by simp)
  have hchain := congrArg (fun L : ℝ →L[ℝ] LoopAmbient => L 1)
    (mfderiv_comp (f 0) hqd hcd)
  have hvelocity : deriv c (f 0) = mfderiv (𝓡 3) (𝓡 3) q
      (periodicFreeLoop gamma (f 0)) (curveVelocity (periodicFreeLoop gamma) (f 0)) := by
    simpa +instances only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv, curveVelocity, c] using! hchain
  have hc0 : deriv c (f 0) ≠ 0 := by
    intro hz
    apply hregular (f 0)
    apply ((mdifferentiable_chart (I := 𝓡 3) (S.disk.map x)).mfderiv hsource).injective
    change mfderiv (𝓡 3) (𝓡 3) q (periodicFreeLoop gamma (f 0))
      (curveVelocity (periodicFreeLoop gamma) (f 0)) =
        mfderiv (𝓡 3) (𝓡 3) q (periodicFreeLoop gamma (f 0)) 0
    rw [← hvelocity, hz, map_zero]
  have hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (f t) := by
    filter_upwards with t
    change q (S.disk.map (P (t : ℂ))) = q (periodicFreeLoop gamma (h (t + a)))
    rw [hP t, hlift]
  obtain ⟨ε, _hε, _hidentity, hT⟩ := halfDisk_boundary_tangent gE hr hm hH hfactor hF hunit
    hcAt hc0 hf hmono hcurve
  exact hT

end PoincareConjecture.M65MinimalDisk
