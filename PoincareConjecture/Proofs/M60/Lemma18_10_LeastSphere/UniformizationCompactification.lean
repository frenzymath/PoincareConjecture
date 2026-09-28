import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationFlatDevelopment










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField Bundle
open ComplexConjugate
open scoped Manifold ContDiff Bundle Topology NNReal

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)



theorem metricComplete_of_proper_exhaustion
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]
    (g : RiemannianMetric 2 M)
    (rho : M → ℝ) (hrho : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ rho)
    (hproper : ∀ r : ℝ, IsCompact (rho ⁻¹' Icc (-r) r))
    (K : ℝ≥0) (hK : 0 < K)
    (hbound : ∀ x v, |mvfderiv (𝓡 2) rho x v| ≤ K * g.tangentNorm x v) :
    MetricComplete g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Plane (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 2) M
  have hLip : LipschitzWith K rho := by
    intro x y
    exact g.edist_le_mul_edist_of_derivative_bound (hrho.of_le (by simp)) hK hbound x y
  change CompleteSpace M
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hcu := hLip.uniformContinuous.comp_cauchySeq hu
  obtain ⟨r, hr⟩ := hcu.isBounded_range.exists_norm_le
  have huin (i : ℕ) : u i ∈ rho ⁻¹' Icc (-r) r := by
    have hb : |rho (u i)| ≤ r := by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hr _ (mem_range_self i)
    exact abs_le.mp hb
  obtain ⟨x, -, phi, hphi, hx⟩ := (hproper r).tendsto_subseq huin
  exact ⟨x, tendsto_nhds_of_cauchySeq_of_subseq hu hphi.tendsto_atTop hx⟩




theorem exists_sphere_compactification (F : Plane ≃ₘ[ℝ] Plane) :
    ∃ H : UnitTwoSphere ≃ₜ UnitTwoSphere,
      H m60SpherePole = m60SpherePole ∧
      (∀ z, H (m60SphereParameter z) = m60SphereParameter (F z)) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H {m60SpherePole}ᶜ ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm {m60SpherePole}ᶜ := by
  have hs : m60SphereChart.symm.source = univ := by simp [m60SphereChart]
  have hemb : Topology.IsEmbedding m60SphereParameter :=
    (m60SphereChart.symm.isOpenEmbedding hs).isEmbedding
  have hr : range m60SphereParameter = {m60SpherePole}ᶜ := by
    simpa [hs, m60SphereParameter, m60SphereChart] using
      m60SphereChart.symm.image_source_eq_target
  let E := OnePoint.equivOfIsEmbeddingOfRangeEq m60SpherePole m60SphereParameter hemb hr
  let H := E.symm.trans (F.toHomeomorph.onePointCongr.trans E)
  have hE (z : Plane) : E (z : OnePoint Plane) = m60SphereParameter z := rfl
  have hEp : E OnePoint.infty = m60SpherePole := rfl
  have hH (z : Plane) : H (m60SphereParameter z) = m60SphereParameter (F z) := by
    rw [← hE z]
    simp only [H, Homeomorph.trans_apply, E.symm_apply_apply]
    rfl
  have hHi (z : Plane) : H.symm (m60SphereParameter z) = m60SphereParameter (F.symm z) := by
    apply H.injective
    rw [H.apply_symm_apply, hH, F.apply_symm_apply]
  have hreg (K : UnitTwoSphere ≃ₜ UnitTwoSphere) (f : Plane → Plane)
      (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f)
      (hK : ∀ z, K (m60SphereParameter z) = m60SphereParameter (f z)) :
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ K {m60SpherePole}ᶜ := by
    intro p hp
    have hps : p ∈ m60SphereChart.source := by simpa [m60SphereChart] using hp
    have hchart : ContMDiffAt (𝓡 2) (𝓡 2) ∞ m60SphereChart p := by
      have hh : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m60SphereChart m60SphereChart.source := by
        rw [m60SphereChart_eq_chartAt]
        exact contMDiffOn_chart
      exact hh.contMDiffAt (m60SphereChart.open_source.mem_nhds hps)
    apply ContMDiffAt.contMDiffWithinAt
    have hh := (m60SphereParameter_contMDiff.comp hf).contMDiffAt.comp p hchart
    apply hh.congr_of_eventuallyEq
    filter_upwards [m60SphereChart.open_source.mem_nhds hps] with q hq
    change K q = m60SphereParameter (f (m60SphereChart q))
    rw [← hK]
    exact congrArg K (m60SphereChart.left_inv hq).symm
  refine ⟨H, ?_, hH, hreg H F F.contMDiff hH, hreg H.symm F.symm F.symm.contMDiff hHi⟩
  rw [← hEp]
  simp only [H, Homeomorph.trans_apply, E.symm_apply_apply]
  rfl

private theorem complex_conformal_directions (L : ℂ →L[ℝ] ℂ) (h : IsConformalMap L) :
    L Complex.I = Complex.I * L 1 ∨ L Complex.I = -Complex.I * L 1 := by
  rcases h.is_complex_or_conj_linear with ⟨K, hK⟩ | ⟨K, hK⟩
  · left
    rw [← hK]
    simpa only [ContinuousLinearMap.coe_restrictScalars', smul_eq_mul, mul_one]
      using K.map_smul Complex.I (1 : ℂ)
  · right
    have h1 : K 1 = L 1 := by
      simpa using congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) hK
    have hi : K Complex.I = -L Complex.I := by
      simpa using congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) hK
    have hm : K Complex.I = Complex.I * K 1 := by
      simpa only [smul_eq_mul, mul_one] using K.map_smul Complex.I (1 : ℂ)
    rw [h1, hi] at hm
    linear_combination -hm

private theorem complex_conformal_orientation
    {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hf : ContDiffOn ℝ ∞ f S) (hc : ∀ z ∈ S, IsConformalMap (fderiv ℝ f z)) :
    (∀ z ∈ S, DifferentiableAt ℂ f z) ∨
      (∀ z ∈ S, DifferentiableAt ℂ (conj ∘ f) z) := by
  let L := fderiv ℝ f
  let sigma : ℂ → ℝ := fun z => (L z Complex.I / L z 1).im
  have hn (z : ℂ) (hz : z ∈ S) : L z 1 ≠ 0 := by
    simpa only [map_zero] using (hc z hz).injective.ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have hd (z : ℂ) (hz : z ∈ S) : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hLc : ContinuousOn L S := hf.continuousOn_fderiv_of_isOpen hS (by simp)
  have hsig : ContinuousOn sigma S := Complex.continuous_im.comp_continuousOn
    ((hLc.clm_apply continuousOn_const).div (hLc.clm_apply continuousOn_const) hn)
  have hside (z : ℂ) (hz : z ∈ S) :
      (sigma z = 1 ∧ L z Complex.I = Complex.I * L z 1) ∨
        (sigma z = -1 ∧ L z Complex.I = -Complex.I * L z 1) := by
    rcases complex_conformal_directions (L z) (hc z hz) with hh | hh
    · exact Or.inl ⟨by dsimp [sigma]; rw [hh, mul_div_cancel_right₀ _ (hn z hz)]; rfl, hh⟩
    · exact Or.inr ⟨by dsimp [sigma]; rw [hh, mul_div_cancel_right₀ _ (hn z hz)]; rfl, hh⟩
  have hsne (z : ℂ) (hz : z ∈ S) : sigma z ≠ 0 := by
    rcases hside z hz with hh | hh <;> rw [hh.1] <;> norm_num
  rcases hSc.mapsTo_Ioi_or_Iio hsig hsne with hpos | hneg
  · left
    intro z hz
    have he : L z Complex.I = Complex.I * L z 1 := by
      rcases hside z hz with hh | hh
      · exact hh.2
      · have h := hpos hz; rw [mem_Ioi, hh.1] at h; norm_num at h
    exact differentiableAt_complex_iff_differentiableAt_real.mpr
      ⟨hd z hz, by simpa only [smul_eq_mul] using he⟩
  · right
    intro z hz
    have he : L z Complex.I = -Complex.I * L z 1 := by
      rcases hside z hz with hh | hh
      · have h := hneg hz; rw [mem_Iio, hh.1] at h; norm_num at h
      · exact hh.2
    have hder := Complex.conjCLE.hasFDerivAt.comp z (hd z hz).hasFDerivAt
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hder.differentiableAt, ?_⟩
    change fderiv ℝ (Complex.conjCLE ∘ f) z Complex.I =
      Complex.I • fderiv ℝ (Complex.conjCLE ∘ f) z 1
    rw [hder.fderiv]
    change conj (L z Complex.I) = Complex.I * conj (L z 1)
    rw [he]
    simp

private theorem complex_punctured_ball_preconnected (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  let e := OpenPartialHomeomorph.univBall c r
  have he : Function.Injective e := (e.isOpenEmbedding (by simp [e])).injective
  have himg : e '' ({0}ᶜ : Set ℂ) = Metric.ball c r \ {c} := by
    rw [compl_eq_univ_sdiff, image_sdiff he]
    have hu : e '' univ = Metric.ball c r := by
      simpa [e, OpenPartialHomeomorph.univBall_target c hr] using e.image_source_eq_target
    rw [hu, image_singleton]
    simp [e]
  rw [← himg]
  apply (isPathConnected_compl_singleton_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank]; norm_num) (0 : ℂ)).isConnected.isPreconnected.image
  exact (OpenPartialHomeomorph.continuous_univBall c r).continuousOn




theorem contDiffAt_of_conformal_punctured
    {f : ℂ → ℂ} {c : ℂ} (hc : ContinuousAt f c)
    (hf : ∀ᶠ z in 𝓝[≠] c, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    ContDiffAt ℝ ∞ f c := by
  obtain ⟨r, hr, hball⟩ := (nhdsWithin_hasBasis Metric.nhds_basis_ball _).mem_iff.mp hf
  have hS : IsOpen (Metric.ball c r \ {c}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hs : ContDiffOn ℝ ∞ f (Metric.ball c r \ {c}) :=
    fun z hz => (hball hz).1.contDiffWithinAt
  have hconf := complex_conformal_orientation hS (complex_punctured_ball_preconnected c hr)
    hs (fun z hz => (hball hz).2)
  have hmem : Metric.ball c r \ {c} ∈ 𝓝[≠] c :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds c hr)) self_mem_nhdsWithin
  rcases hconf with h | h
  · exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (Filter.Eventually.mono hmem h) hc).contDiffAt.restrict_scalars ℝ
  · have ha : ContDiffAt ℝ ∞ (conj ∘ f) c :=
      (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (Filter.Eventually.mono hmem h)
      (Complex.continuous_conj.continuousAt.comp hc)).contDiffAt.restrict_scalars ℝ
    have h := Complex.conjCLE.contDiff.contDiffAt.comp c ha
    change ContDiffAt ℝ ∞ (fun x => conj (conj (f x))) c at h
    simpa only [Complex.conj_conj] using h

private theorem plane_conformal_removal {f : Plane → Plane} {a : Plane}
    (hc : ContinuousAt f a)
    (hf : ∀ᶠ z in 𝓝[≠] a, ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z)) :
    ContDiffAt ℝ ∞ f a := by
  let C := Complex.orthonormalBasisOneI.repr
  let F : ℂ → ℂ := fun z => C.symm (f (C z))
  have he : C (C.symm a) = a := C.apply_symm_apply a
  have hFc : ContinuousAt F (C.symm a) := C.symm.continuous.continuousAt.comp
    ((he ▸ hc).comp C.continuous.continuousAt)
  have hFs : ContDiffAt ℝ ∞ F (C.symm a) := contDiffAt_of_conformal_punctured hFc (by
    rw [eventually_nhdsWithin_iff]
    have ht : Tendsto C (𝓝 (C.symm a)) (𝓝 a) := by
      simpa only [he] using C.continuous.tendsto (C.symm a)
    have hf' : ∀ᶠ z in 𝓝 a, z ≠ a →
        ContDiffAt ℝ ∞ f z ∧ IsConformalMap (fderiv ℝ f z) :=
      eventually_nhdsWithin_iff.mp hf
    filter_upwards [ht.eventually hf'] with z hz hzne
    have hz' : C z ≠ a := fun h => hzne (C.injective (h.trans he.symm))
    obtain ⟨hs, hd⟩ := hz hz'
    have hD := C.symm.toContinuousLinearEquiv.hasFDerivAt.comp z
      ((hs.differentiableAt (by simp)).hasFDerivAt.comp z C.toContinuousLinearEquiv.hasFDerivAt)
    change HasFDerivAt (C.symm ∘ f ∘ C) _ z at hD
    refine ⟨C.symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (hs.comp z C.toContinuousLinearEquiv.contDiff.contDiffAt), ?_⟩
    change IsConformalMap (fderiv ℝ (C.symm ∘ f ∘ C) z)
    rw [hD.fderiv]
    exact C.symm.toLinearIsometry.isConformalMap.comp
      (hd.comp C.toLinearIsometry.isConformalMap))
  have h := C.toContinuousLinearEquiv.contDiff.contDiffAt.comp a
    (hFs.comp a C.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  change ContDiffAt ℝ ∞ (fun x => C (C.symm (f (C (C.symm x))))) a at h
  simpa only [C.apply_symm_apply] using h



theorem contMDiffAt_conformal_sphere_puncture
    (g q : RiemannianMetric 2 UnitTwoSphere) (H : UnitTwoSphere ≃ₜ UnitTwoSphere)
    (p : UnitTwoSphere)
    (hs : ∀ x ≠ p, ContMDiffAt (𝓡 2) (𝓡 2) ∞ H x)
    (hc : ∀ x ≠ p, ∃ c : ℝ, 0 < c ∧ ∀ v w,
      q.inner (H x) (mfderiv (𝓡 2) (𝓡 2) H x v) (mfderiv (𝓡 2) (𝓡 2) H x w) =
        c * g.inner x v w) : ContMDiffAt (𝓡 2) (𝓡 2) ∞ H p := by
  obtain ⟨Dg⟩ := m01_exists_leviCivitaData g
  obtain ⟨Dq⟩ := m01_exists_leviCivitaData q
  obtain ⟨e, a, l, ha, hap, he, hei, -, hl, hge⟩ :=
    exists_isothermal_chart_compact_surface g Dg p
  obtain ⟨d, b, k, hb, hbp, hd, hdi, -, hk, hqd⟩ :=
    exists_isothermal_chart_compact_surface q Dq (H p)
  have hpt : p ∈ e.target := hap ▸ e.map_source ha
  have hHt : H p ∈ d.target := hbp ▸ d.map_source hb
  let B : Plane → Plane := d.symm ∘ H ∘ e
  have hepa : e.symm p = a := by rw [← hap, e.left_inv ha]
  have hBap : B a = b := by dsimp [B]; rw [hap, ← hbp, d.left_inv hb]
  have hEa : Tendsto e (𝓝 a) (𝓝 p) := by
    simpa only [hap] using (e.continuousAt ha).tendsto
  have htargets : ∀ᶠ z in 𝓝 a, z ∈ e.source ∧ H (e z) ∈ d.target := by
    apply Filter.Eventually.and (e.open_source.mem_nhds ha)
    exact ((H.continuous.tendsto p).comp hEa).eventually (d.open_target.mem_nhds hHt)
  have hHt' : H (e a) ∈ d.target := by rwa [hap]
  have hBc : ContinuousAt B a := by
    exact (d.symm.continuousAt hHt').tendsto.comp
      ((H.continuous.tendsto (e a)).comp (e.continuousAt ha).tendsto)
  have hBs : ContDiffAt ℝ ∞ B a := plane_conformal_removal hBc (by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [htargets] with z hz hza
    have hzp : e z ≠ p := fun h => hza (e.injOn hz.1 ha (h.trans hap.symm))
    have hes := he.contMDiffAt (e.open_source.mem_nhds hz.1)
    have hHs := hs (e z) hzp
    have hdis := hdi.contMDiffAt (d.open_target.mem_nhds hz.2)
    have hBz : ContMDiffAt (𝓡 2) (𝓡 2) ∞ B z := hdis.comp z (hHs.comp z hes)
    refine ⟨contMDiffAt_iff_contDiffAt.mp hBz, ?_⟩
    obtain ⟨c, hcp, hci⟩ := hc (e z) hzp
    have hdif : d.MDifferentiable (𝓡 2) (𝓡 2) :=
      ⟨hd.mdifferentiableOn (by simp), hdi.mdifferentiableOn (by simp)⟩
    have hDB : fderiv ℝ B z = (mfderiv (𝓡 2) (𝓡 2) d.symm (H (e z))).comp
        ((mfderiv (𝓡 2) (𝓡 2) H (e z)).comp (mfderiv (𝓡 2) (𝓡 2) e z)) := by
      rw [← mfderiv_eq_fderiv]
      exact (mfderiv_comp z (hdis.mdifferentiableAt (by simp))
        ((hHs.comp z hes).mdifferentiableAt (by simp))).trans
        (congrArg _ (mfderiv_comp z (hHs.mdifferentiableAt (by simp))
          (hes.mdifferentiableAt (by simp))))
    have hchain (v : Plane) : mfderiv (𝓡 2) (𝓡 2) d (B z) (fderiv ℝ B z v) =
        mfderiv (𝓡 2) (𝓡 2) H (e z) (mfderiv (𝓡 2) (𝓡 2) e z v) := by
      rw [hDB]
      exact congrArg (fun T => T (mfderiv (𝓡 2) (𝓡 2) H (e z)
        (mfderiv (𝓡 2) (𝓡 2) e z v))) (hdif.comp_symm_deriv hz.2)
    have hBsrc : B z ∈ d.source := d.map_target hz.2
    apply (isConformalMap_iff (fderiv ℝ B z)).mpr
    refine ⟨c * l z / k (B z), div_pos (mul_pos hcp (hl z hz.1)) (hk _ hBsrc), ?_⟩
    intro v w
    have hm := hqd (B z) hBsrc (fderiv ℝ B z v) (fderiv ℝ B z w)
    change q.inner (d (B z))
      (mfderiv (𝓡 2) (𝓡 2) d (B z) (fderiv ℝ B z v))
      (mfderiv (𝓡 2) (𝓡 2) d (B z) (fderiv ℝ B z w)) = _ at hm
    have hBpoint : d (B z) = H (e z) := d.right_inv hz.2
    rw [hchain v, hchain w] at hm
    erw [hBpoint, hci] at hm
    change c * g.pullbackCoefficients e z v w = _ at hm
    erw [hge z hz.1 v w] at hm
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hk _ hBsrc).ne').mpr
    linear_combination -hm
    )
  have hBp : ContMDiffAt (𝓡 2) (𝓡 2) ∞ B (e.symm p) := by
    rw [hepa]
    exact contMDiffAt_iff_contDiffAt.mpr hBs
  have hD : ContMDiffAt (𝓡 2) (𝓡 2) ∞ d (B (e.symm p)) := by
    rw [hepa, hBap]
    exact hd.contMDiffAt (d.open_source.mem_nhds hb)
  have hfull := hD.comp p (hBp.comp p (hei.contMDiffAt (e.open_target.mem_nhds hpt)))
  apply hfull.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hpt,
    H.continuous.continuousAt (d.open_target.mem_nhds hHt)] with x hx hHx
  change H x = d (d.symm (H (e (e.symm x))))
  rw [e.right_inv hx, d.right_inv hHx]



theorem diffeomorph_of_conformal_sphere_puncture
    (g q : RiemannianMetric 2 UnitTwoSphere) (H : UnitTwoSphere ≃ₜ UnitTwoSphere)
    (p : UnitTwoSphere)
    (hs : ∀ x ≠ p, ContMDiffAt (𝓡 2) (𝓡 2) ∞ H x)
    (hi : ∀ x ≠ H p, ContMDiffAt (𝓡 2) (𝓡 2) ∞ H.symm x)
    (hc : ∀ x ≠ p, ∃ c : ℝ, 0 < c ∧ ∀ v w,
      q.inner (H x) (mfderiv (𝓡 2) (𝓡 2) H x v) (mfderiv (𝓡 2) (𝓡 2) H x w) =
        c * g.inner x v w) :
    ∃ phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere, (phi : _ → _) = H := by
  have hci (x : UnitTwoSphere) (hx : x ≠ H p) : ∃ c : ℝ, 0 < c ∧ ∀ v w,
      g.inner (H.symm x) (mfderiv (𝓡 2) (𝓡 2) H.symm x v)
        (mfderiv (𝓡 2) (𝓡 2) H.symm x w) = c * q.inner x v w := by
    have hy : H.symm x ≠ p := fun he => hx (by rw [← he, H.apply_symm_apply])
    obtain ⟨c, hcp, hcm⟩ := hc (H.symm x) hy
    have hd := mfderiv_comp x ((hs _ hy).mdifferentiableAt (by simp))
      ((hi x hx).mdifferentiableAt (by simp))
    have heq : (H : _ → _) ∘ H.symm = id := funext H.apply_symm_apply
    rw [heq, mfderiv_id] at hd
    have hchain (v : TangentSpace (𝓡 2) x) := congrArg (fun L => L v) hd.symm
    refine ⟨c⁻¹, inv_pos.mpr hcp, fun v w => ?_⟩
    have hm := hcm (mfderiv (𝓡 2) (𝓡 2) H.symm x v)
      (mfderiv (𝓡 2) (𝓡 2) H.symm x w)
    erw [H.apply_symm_apply, hchain v, hchain w] at hm
    change q.inner x v w = _ at hm
    rw [hm, ← mul_assoc, inv_mul_cancel₀ hcp.ne', one_mul]
  have hHs : ContMDiff (𝓡 2) (𝓡 2) ∞ H := fun x => by
    by_cases hx : x = p
    · subst x; exact contMDiffAt_conformal_sphere_puncture g q H p hs hc
    · exact hs x hx
  have hHi : ContMDiff (𝓡 2) (𝓡 2) ∞ H.symm := fun x => by
    by_cases hx : x = H p
    · subst x; exact contMDiffAt_conformal_sphere_puncture q g H.symm (H p) hi hci
    · exact hi x hx
  exact ⟨⟨H.toEquiv, hHs, hHi⟩, rfl⟩
end PoincareConjecture.M60

end
