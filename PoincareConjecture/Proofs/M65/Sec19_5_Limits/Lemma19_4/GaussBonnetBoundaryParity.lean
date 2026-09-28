import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryOrder
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetMinimalDiskBoundary
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetResidualPlane
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaBoundaryLength













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex InnerProductSpace MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace

private theorem exists_pairing_nonzero_two {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ L : E →L[ℝ] ℝ, L v ≠ 0 ∧ L w ≠ 0 := by
  by_cases h : inner ℝ v w = 0
  · have h' : inner ℝ w v = 0 := (real_inner_comm v w).trans h
    refine ⟨innerSL ℝ (v + w), ?_, ?_⟩
    · change inner ℝ (v + w) v ≠ 0
      rw [inner_add_left, h', add_zero]
      exact (real_inner_self_pos.mpr hv).ne'
    · change inner ℝ (v + w) w ≠ 0
      rw [inner_add_left, h, zero_add]
      exact (real_inner_self_pos.mpr hw).ne'
  · exact ⟨innerSL ℝ v, (real_inner_self_pos.mpr hv).ne', h⟩

private theorem even_order_of_monotone_vector_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℝ → ℝ} {V A : ℝ → E} {m : ℕ}
    (hf : Monotone f ∨ Antitone f) (hV : ContinuousAt V 0) (hA : ContinuousAt A 0)
    (hV0 : V 0 ≠ 0) (hA0 : A 0 ≠ 0)
    (hfactor : ∀ᶠ t in 𝓝 (0 : ℝ), deriv f t • V t = t ^ m • A t) : Even m := by
  obtain ⟨L, hLV, hLA⟩ := exists_pairing_nonzero_two hV0 hA0
  let q := fun t => L (A t) / L (V t)
  have hLVc : ContinuousAt (fun t => L (V t)) 0 := L.continuous.continuousAt.comp hV
  have hqc : ContinuousAt q 0 :=
    (L.continuous.continuousAt.comp hA).div hLVc hLV
  have hq0 : q 0 ≠ 0 := div_ne_zero hLA hLV
  apply even_order_of_monotone_derivative hf hqc hq0
  filter_upwards [hfactor, hLVc.eventually_ne hLV] with t ht hn
  have hh := congrArg L ht
  simp only [map_smul, smul_eq_mul] at hh
  dsimp only [q]
  rw [← mul_div_assoc]
  apply (eq_div_iff hn).mpr
  exact hh

private theorem residual_columns_halfDiskGradient {n : ℕ}
    (H : ℂ → EuclideanSpace ℝ (Fin n)) (r : ℝ) (z : ℂ) :
    residualRealColumn (halfDiskGradient H r z) =
        fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z 1 ∧
      residualImagColumn (halfDiskGradient H r z) =
        fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z I := by
  let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
  simpa only [complexGradient, T.fderiv, T, halfDiskGradient] using
    residual_columns_complexGradient T 0

private theorem halfDisk_residual_real_ne_zero {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ : ContinuousOn Q (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ0 : Q 0 ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0) : residualRealColumn (Q 0) ≠ 0 := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let A := fun z => residualRealColumn (Q z)
  let B := fun z => residualImagColumn (Q z)
  let G := fun z => g.euclideanCoefficients (H z)
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hcl : K ⊆ closure W := by
    rw [(halfDisk_differential_domain hr).2.2.2]
  have hAc : ContinuousOn A K := residualRealColumn.continuous.comp_continuousOn hQ
  have hBc : ContinuousOn B K := residualImagColumn.continuous.comp_continuousOn hQ
  have hGc : ContinuousOn G K :=
    ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).continuous).comp_continuousOn
      hH.continuousOn
  have hdiagW : EqOn (fun z => G z (B z) (B z)) (fun z => G z (A z) (A z)) W := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro he
      have hh : 0 < z.im := hz.2
      simp only [he, zero_im, lt_self_iff_false] at hh
    obtain ⟨ha, hb⟩ := residual_columns_halfDiskGradient H r z
    rw [hfactor z (hWK hz)] at ha hb
    have hc := hconf z (hWK hz)
    change G z (fderivWithin ℝ H K z 1) (fderivWithin ℝ H K z 1) =
        G z (fderivWithin ℝ H K z I) (fderivWithin ℝ H K z I) ∧
      G z (fderivWithin ℝ H K z 1) (fderivWithin ℝ H K z I) = 0 at hc
    exact (residual_columns_conformal_of_smul (G z) (fun v w => g.symm (H z) v w)
      (pow_ne_zero m hzne) (Q z)
      (by simpa only [ha, hb] using hc.2)
      (by simpa only [ha, hb] using hc.1.symm)).2
  have hdiagK := hdiagW.of_subset_closure ((hGc.clm_apply hBc).clm_apply hBc)
    ((hGc.clm_apply hAc).clm_apply hAc) hWK hcl
  have h0 : (0 : ℂ) ∈ K := ⟨mem_closedBall_self hr.le, by simp⟩
  have hp := residual_columns_factor_pos (G 0) (fun v hv => g.pos (H 0) v hv)
    hQ0 (hdiagK h0)
  intro hzero
  rw [hzero, map_zero] at hp
  exact (lt_irrefl 0) hp






theorem halfDisk_monotone_boundary_factor_even {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ : ContinuousOn Q (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hQ0 : Q 0 ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {f : ℝ → ℝ}
    (hc : ContDiffAt ℝ 2 c (f 0)) (hc0 : deriv c (f 0) ≠ 0)
    (hf : ContDiff ℝ 1 f) (hmono : Monotone f ∨ Antitone f)
    (hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (f t)) : Even m := by
  let V := fun t => deriv c (f t)
  let A := fun t : ℝ => residualRealColumn (Q (t : ℂ))
  have hV : ContinuousAt V 0 := by
    have hd : ContinuousAt (deriv c) (f 0) :=
      ((hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).continuousAt
    exact hd.comp hf.continuous.continuousAt
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < r :=
    (continuous_ofReal.norm.continuousAt).eventually (gt_mem_nhds (by simpa using hr))
  have hA : ContinuousAt A 0 := by
    have hQr : ContinuousOn (fun t : ℝ => Q (t : ℂ)) (Ioo (-r) r) :=
      hQ.comp continuous_ofReal.continuousOn (fun t ht => by
        refine ⟨mem_closedBall_zero_iff.mpr ?_, by simp⟩
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_lt.mpr ⟨ht.1, ht.2⟩).le)
    exact residualRealColumn.continuous.continuousAt.comp
      (hQr.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩))
  have hA0 : A 0 ≠ 0 := by
    simpa only [A, ofReal_zero] using halfDisk_residual_real_ne_zero g hr m hH hQ hQ0 hfactor hconf
  apply even_order_of_monotone_vector_derivative hmono hV hA hc0 hA0
  have hcd : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ c (f t) :=
    hf.continuous.continuousAt.eventually ((hc.eventually (by norm_num)).mono
      (fun _ ht => ht.differentiableAt (by norm_num)))
  filter_upwards [hnear, hcd, hcurve.eventually_nhds] with t ht hct hcurvet
  have hK : (t : ℂ) ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im} :=
    ⟨mem_closedBall_zero_iff.mpr ht.le, by simp⟩
  have hD := (hct.hasDerivAt.scomp t (hf.differentiable one_ne_zero t).hasDerivAt)
  have hce : (fun s : ℝ => H (s : ℂ)) =ᶠ[𝓝 t] c ∘ f := hcurvet
  have hdiam := (halfDisk_hasDerivAt_diameter hH ht).congr_of_eventuallyEq hce.symm
  have hactual := hD.unique hdiam
  change deriv f t • V t = _ at hactual
  obtain ⟨hreal, _himag⟩ := residual_columns_halfDiskGradient H r (t : ℂ)
  rw [hfactor (t : ℂ) hK, (residual_columns_smul _ _).1] at hreal
  simp only [← Complex.ofReal_pow, ofReal_re, ofReal_im, zero_smul, add_zero] at hreal
  exact hactual.trans hreal.symm

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}






theorem boundary_differential_order_even (S : M65MinimalDisk g connection gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1)
    (gE : RiemannianMetric 3 LoopAmbient) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (Q : ℂ → Fin 3 → ℂ) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ boundaryCoordinate (e.symm x)
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    ContDiffOn ℝ 1 H K → ContinuousOn Q K → Q 0 ≠ 0 →
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) →
      (∀ z ∈ K,
        let T := fderivWithin ℝ H K z
        gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
          gE.inner (H z) (T 1) (T I) = 0) → Even m := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let q := chartAt LoopAmbient (S.disk.map x)
  let P := e ∘ boundaryCoordinate p
  let H := q ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  change ContDiffOn ℝ 1 H K → ContinuousOn Q K → Q 0 ≠ 0 →
    (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) →
    (∀ z ∈ K,
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0) → Even m
  intro hH hQ hQ0 hfactor hconf
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  let a := Complex.arg p
  have he : Complex.exp ((a : ℂ) * I) = p := by
    simpa only [hp, ofReal_one, one_mul, a] using Complex.norm_mul_exp_arg_mul_I p
  have hangular (t : ℝ) : e.symm (Proofs.M58.angularPoint t) =
      Complex.exp ((t : ℂ) * I) := by
    rw [Complex.exp_ofReal_mul_I]
    rfl
  have hP (t : ℝ) : P (t : ℂ) = Proofs.M58.angularPoint (t + a) := by
    apply e.symm.injective
    change e.symm (e (boundaryCoordinate p (t : ℂ))) = _
    rw [e.symm_apply_apply, hangular, ofReal_add, add_mul, Complex.exp_add, he]
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
  apply halfDisk_monotone_boundary_factor_even gE hr m hH hQ hQ0 hfactor hconf
    hcAt hc0 hf hmono
  filter_upwards with t
  change q (S.disk.map (P (t : ℂ))) = q (periodicFreeLoop gamma (h (t + a)))
  rw [hP t, hlift]






theorem boundary_branch_residual_even_holder (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧ Even m ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      MemLp (fun z => fderiv ℝ Q z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ Q z Complex.I) 2 (volume.restrict W) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖Q z - Q w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  obtain ⟨gE, DE, r, m, Q, hr, hmap, hsource, hH, hHi, hmetric, hnorm,
      heq, hQ, hQ1, hQne, hfactor, hDQ1, hDQI, hholder⟩ :=
    S.boundary_branch_residual_holder hinj hsmooth hregular hx
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ boundaryCoordinate p
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have hconf (z : ℂ) (hz : z ∈ K) :
      let T := fderivWithin ℝ H K z
      gE.inner (H z) (T 1) (T 1) = gE.inner (H z) (T I) (T I) ∧
        gE.inner (H z) (T 1) (T I) = 0 := by
    let T := fderivWithin ℝ H K z
    have h1 := hnorm z hz 1
    have hI := hnorm z hz I
    have hsum := hnorm z hz (1 + I)
    have hs : ‖(1 : ℂ) + I‖ ^ 2 = 2 := by
      norm_num [Complex.sq_norm, Complex.normSq_apply]
    simp only [norm_one, norm_I, one_pow, mul_one] at h1 hI
    rw [hs, map_add] at hsum
    change gE.inner (H z) (T 1 + T I) (T 1 + T I) = _ at hsum
    simp only [map_add, add_apply] at hsum
    rw [gE.symm (H z) (T I) (T 1)] at hsum
    exact ⟨h1.trans hI.symm, by linarith⟩
  have hperiodic : periodicFreeLoop gamma = gamma ∘ m65LoopAngular := by
    funext t
    exact gamma.boundary (m65LoopAngular t)
  have h0 : (0 : ℂ) ∈ K := ⟨mem_closedBall_self hr.le, by simp⟩
  have heven := S.boundary_differential_order_even (hperiodic ▸ hsmooth)
    (hperiodic ▸ hregular) hx gE hr m Q hH hQ (hQne 0 h0) hfactor hconf
  exact ⟨gE, DE, r, m, Q, hr, heven, hmap, hsource, hH, hHi, hmetric,
    hnorm, heq, hQ, hQ1, hQne, hfactor, hDQ1, hDQI, hholder⟩




theorem boundary_branch_residual_even (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let p := e.symm x
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate p
    let H := chart ∘ S.disk.map ∘ P
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
      (r : ℝ) (m : ℕ) (Q : ℂ → Fin 3 → ℂ), 0 < r ∧ Even m ∧
      let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
      MapsTo P K loopDiskSet ∧ MapsTo (S.disk.map ∘ P) K chart.source ∧
      ContDiffOn ℝ 1 H K ∧ ContDiffOn ℝ ∞ H W ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) ∧
      (∀ z ∈ K, ∀ v : ℂ,
        gE.inner (H z) (fderivWithin ℝ H K z v) (fderivWithin ℝ H K z v) =
          diskConformalFactor g S.disk.map (P z) *
            ‖Complex.I * boundaryCoordinate p z‖ ^ 2 * ‖v‖ ^ 2) ∧
      (∀ z ∈ W, dbar (complexGradient H) z =
        harmonicMatrix DE H z (complexGradient H z)) ∧
      ContinuousOn Q K ∧ ContDiffOn ℝ 1 Q W ∧
      (∀ z ∈ K, Q z ≠ 0) ∧
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) ∧
      MemLp (fun z => fderiv ℝ Q z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ Q z Complex.I) 2 (volume.restrict W) := by
  obtain ⟨gE, DE, r, m, Q, hr, hm, hP, hsrc, hH, hHi, hg, hn, heq,
      hQc, hQi, hQne, hf, h1, hI, _⟩ :=
    S.boundary_branch_residual_even_holder hinj hsmooth hregular hx
  exact ⟨gE, DE, r, m, Q, hr, hm, hP, hsrc, hH, hHi, hg, hn, heq,
    hQc, hQi, hQne, hf, h1, hI⟩

end PoincareConjecture.M65MinimalDisk
