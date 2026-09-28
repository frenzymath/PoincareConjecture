import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTargetChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHalfConeEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityACComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap ENNReal

universe u

namespace PoincareConjecture.M65Boundary

open M65Interior M65StrictTrace

theorem punctured_curve_regular {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (γ : LoopCircle → M)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hreg : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0) (p : LoopCircle) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ puncturedArc p) ∧
      curveVelocity (n := 3) (γ ∘ puncturedArc p) 0 ≠ 0 := by
  let v := -Complex.orthonormalBasisOneI.repr.symm (p : LoopPlane)
  let a := Complex.arg v
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_neg, LinearIsometryEquiv.norm_map, p.property]
  have he : Complex.exp ((a : ℂ) * Complex.I) = v := by
    simpa only [hv, Complex.ofReal_one, one_mul, a] using Complex.norm_mul_exp_arg_mul_I v
  have hangular (t : ℝ) :
      Complex.orthonormalBasisOneI.repr.symm (m65LoopAngular t : LoopPlane) =
        Complex.exp ((t : ℂ) * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I]
    rfl
  have harc (t : ℝ) : puncturedArc p t = m65LoopAngular (t + a) := by
    apply Subtype.ext
    apply Complex.orthonormalBasisOneI.repr.symm.injective
    change Complex.orthonormalBasisOneI.repr.symm
      (Complex.orthonormalBasisOneI.repr (boundaryCoordinate v t)) = _
    rw [LinearIsometryEquiv.symm_apply_apply, hangular, Complex.ofReal_add,
      add_mul, Complex.exp_add, he]
    simp only [boundaryCoordinate, mul_comm Complex.I (t : ℂ), mul_comm v]
  have hfun : γ ∘ puncturedArc p = (γ ∘ m65LoopAngular) ∘ (fun t : ℝ => t + a) := by
    funext t
    simp only [Function.comp_apply, harc]
  have hs : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => t + a) :=
    (contDiff_id.add contDiff_const).contMDiff
  rw [hfun]
  refine ⟨hγ.comp hs, ?_⟩
  have hchain := congrArg (fun L : ℝ →L[ℝ] LoopAmbient => L 1)
    (mfderiv_comp 0 ((hγ (0 + a)).mdifferentiableAt (by simp))
      ((hs 0).mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at hchain
  change curveVelocity ((γ ∘ m65LoopAngular) ∘ (fun t : ℝ => t + a)) 0 =
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) (γ ∘ m65LoopAngular) (0 + a)
      (fderiv ℝ (fun t : ℝ => t + a) 0 1) at hchain
  have hder : deriv (fun t : ℝ => t + a) 0 = 1 := by
    simpa only [id_eq] using ((hasDerivAt_id 0).add_const a).deriv
  rw [fderiv_apply_one_eq_deriv, hder, zero_add] at hchain
  rw [hchain]
  exact hreg a

theorem exists_captured_boundary_target_chart {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (γ : LoopCircle → M)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hreg : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0) (p : LoopCircle) :
    ∃ (j : Fin 3) (H : EuclideanSpace ℝ (Fin N) → LoopAmbient)
      (A : LoopAmbient → M) (L : NNReal) (ρ δ K : ℝ)
      (E : OpenPartialHomeomorph LoopCircle ℝ),
      0 < ρ ∧ 0 < δ ∧ 0 < K ∧ puncturedArc p 0 ∈ E.source ∧
      Convex ℝ E.target ∧ H (e (γ (puncturedArc p 0))) = 0 ∧
      ContDiff ℝ 1 H ∧ LipschitzWith L H ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ K) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) 1 A (ball 0 (2 * ρ)) ∧
      (∀ y ∈ closedBall (0 : LoopAmbient) ρ, ‖fderiv ℝ (e ∘ A) y‖ ≤ K) ∧
      (∀ q : M, dist (e q) (e (γ (puncturedArc p 0))) < δ →
        ‖H (e q)‖ < ρ / 4 ∧ A (H (e q)) = q) ∧
      (∀ z ∈ E.source, H (e (γ z)) = E z • EuclideanSpace.basisFun (Fin 3) ℝ j) ∧
      ∀ t ∈ E.target, A (t • EuclideanSpace.basisFun (Fin 3) ℝ j) = γ (E.symm t) := by
  obtain ⟨hC, hC0⟩ := punctured_curve_regular γ hγ hreg p
  obtain ⟨j, H, A, L, ρ, δ, η, K, hρ, hδ, hη, hK, hH0, _hA0,
    hH, hLip, hHD, hA, hAD, hcap, haxis⟩ :=
      exists_bounded_boundary_target_chart e he hinj hemb (γ ∘ puncturedArc p) hC 0 hC0
  let E0 := circleArgChart p
  let E := (E0.symm.restrOpen (Ioo (-η) η) isOpen_Ioo).symm
  have htarget : E.target = Ioo (-Real.pi) Real.pi ∩ Ioo (-η) η := rfl
  have ht0 : (0 : ℝ) ∈ E.target := by
    rw [htarget]
    exact ⟨⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩, ⟨neg_neg_of_pos hη, hη⟩⟩
  have hsrc0 : puncturedArc p 0 ∈ E.source := E.map_target ht0
  refine ⟨j, H, A, L, ρ, δ, K, E, hρ, hδ, hK, hsrc0,
    htarget ▸ (convex_Ioo _ _).inter (convex_Ioo _ _), hH0,
    hH, hLip, hHD, hA, hAD, hcap, ?_, ?_⟩
  · intro z hz
    have ht := E.map_source hz
    rw [htarget] at ht
    have h := (haxis (E z) (by simpa only [zero_sub, zero_add] using ht.2)).1
    have hEq : puncturedArc p (E z) = z := E.left_inv hz
    simpa only [Function.comp_apply, sub_zero, hEq] using h
  · intro t ht
    rw [htarget] at ht
    change A (t • EuclideanSpace.basisFun (Fin 3) ℝ j) = γ (puncturedArc p t)
    simpa only [Function.comp_apply, sub_zero] using
      (haxis t (by simpa only [zero_sub, zero_add] using ht.2)).2

private theorem semicircle_coordinate_data {N : ℕ}
    (H : EuclideanSpace ℝ (Fin N) → LoopAmbient) {L : NNReal} {K : ℝ}
    (hH : ContDiff ℝ 1 H) (hLip : LipschitzWith L H)
    (hHD : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    {V W : ℝ → EuclideanSpace ℝ (Fin N)}
    (hV : AbsolutelyContinuousOnInterval V 0 Real.pi)
    (hW : MemLp W 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      V t - V s = ∫ θ in s..t, W θ) :
    let v := H ∘ V
    let d := fun θ => fderiv ℝ H (V θ) (W θ)
    AbsolutelyContinuousOnInterval v 0 Real.pi ∧
      MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
      (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
        v t - v s = ∫ θ in s..t, d θ) ∧
      (∫ θ in Icc (0 : ℝ) Real.pi, ‖d θ‖ ^ 2) ≤
        K ^ 2 * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2 := by
  let v := H ∘ V
  let d := fun θ => fderiv ℝ H (V θ) (W θ)
  have hVC : ContinuousOn V (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hV.continuousOn
  have hDb (θ : ℝ) : ‖d θ‖ ≤ K * ‖W θ‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hHD _) (norm_nonneg _))
  have hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) := by
    apply hW.of_le_mul _ (ae_of_all _ hDb)
    have hcoeff : AEStronglyMeasurable (fun θ => fderiv ℝ H (V θ))
        (volume.restrict (Icc (0 : ℝ) Real.pi)) :=
      ((hH.continuous_fderiv one_ne_zero).comp_continuousOn hVC).aestronglyMeasurable
        measurableSet_Icc
    have happ : Continuous (fun z :
        (EuclideanSpace ℝ (Fin N) →L[ℝ] LoopAmbient) × EuclideanSpace ℝ (Fin N) => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    exact happ.comp_aestronglyMeasurable (hcoeff.prodMk hW.1)
  have hWIcc : IntegrableOn W (Icc (0 : ℝ) Real.pi) :=
    hW.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hWI : IntervalIntegrable W volume 0 Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.pi_pos.le).mpr hWIcc
  refine ⟨ac_comp_lipschitz hV hLip.lipschitzOnWith (mapsTo_univ _ _), hd, ?_, ?_⟩
  · intro s hs t ht
    have hdIcc : IntegrableOn d (Icc (0 : ℝ) Real.pi) :=
      hd.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hdi : IntervalIntegrable d volume s t :=
      (hdIcc.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
    ext j
    let pr : LoopAmbient →L[ℝ] ℝ := EuclideanSpace.proj j
    have hj (θ : ℝ) : fderiv ℝ (pr ∘ H) (V θ) (W θ) = pr (d θ) := by
      rw [(pr.hasFDerivAt.comp (V θ) ((hH.differentiable one_ne_zero _).hasFDerivAt)).fderiv]
      rfl
    have hi := (ac_chain_integral Real.pi_pos hV
      (pr.lipschitz.comp hLip).lipschitzOnWith (mapsTo_univ _ _)
      (fun θ _ => pr.differentiableAt.comp _ (hH.differentiable one_ne_zero _)) hWI hinc).2.2.2
        s hs t ht
    change pr (H (V t)) - pr (H (V s)) = pr (∫ θ in s..t, d θ)
    rw [← pr.intervalIntegral_comp_comm hdi]
    simpa only [Function.comp_apply, hj] using hi
  · rw [← integral_const_mul]
    apply integral_mono_ae hd.norm.integrable_sq (hW.norm.integrable_sq.const_mul _)
    exact ae_of_all _ fun θ => by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hDb θ) 2

private theorem boundaryCirclePoint_joint_continuous :
    Continuous (fun z : LoopCircle × ℝ => boundaryCirclePoint
      (p := Complex.orthonormalBasisOneI.repr.symm (z.1 : LoopPlane))
      (by rw [LinearIsometryEquiv.norm_map]; exact z.1.property) z.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : LoopCircle × ℝ => Complex.orthonormalBasisOneI.repr
    (Complex.orthonormalBasisOneI.repr.symm (z.1 : LoopPlane) *
      Complex.exp (Complex.I * Complex.orthonormalBasisOneI.repr.symm
        (z.2 • EuclideanSpace.basisFun (Fin 2) ℝ 0))))
  fun_prop

set_option maxHeartbeats 2000000 in

theorem boundary_small_semicircle_comparison_uniform {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p0 : ℂ} (hp0 : ‖p0‖ = 1) :
    ∃ R δ B η : ℝ, 0 < R ∧ 0 < δ ∧ 0 < B ∧ 0 < η ∧
      ∀ {p : ℂ} (hp : ‖p‖ = 1), dist p p0 < η → ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      MemLp (fun z => e (F.value (P z))) 2 (volume.restrict S) →
      (∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S)) →
      ∀ V W : ℝ → EuclideanSpace ℝ (Fin N),
        AbsolutelyContinuousOnInterval V 0 Real.pi →
        MapsTo V (Icc (0 : ℝ) Real.pi) (range e) →
        V 0 = e (γ (F.parameter (boundaryCirclePoint hp r))) →
        V Real.pi = e (γ (F.parameter (boundaryCirclePoint hp (-r)))) →
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) →
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          V t - V s = ∫ θ in s..t, W θ) →
        (∀ θ ∈ Icc (0 : ℝ) Real.pi, ‖V θ - V 0‖ < δ) →
        (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in S, weakDiskBoundaryField F p i z j * test z + e (F.value (P z)) j *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
              r * (∫ θ in (0 : ℝ)..Real.pi,
                V θ j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                  test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
          (weakDiskBoundaryField F p) z) ≤ B * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2 := by
  classical
  let b0 := F.parameter (boundaryCirclePoint hp0 0)
  let targetPuncture : LoopCircle := ⟨-(b0 : LoopPlane), by simp only [norm_neg, b0.property]⟩
  have htarget0 : puncturedArc targetPuncture 0 = b0 := by
    apply Subtype.ext
    change Complex.orthonormalBasisOneI.repr
      (boundaryCoordinate (-Complex.orthonormalBasisOneI.repr.symm (-(b0 : LoopPlane))) 0) = b0
    simp only [map_neg, neg_neg, boundaryCoordinate,
      mul_zero, Complex.exp_zero, mul_one, LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨j, H, A, L, ρ, δ0, K, E, hρ, hδ, hK, hEc, hconv, _hH0,
    hH, hLip, hHD, hA, hAD, hcapture, haxis, haxisInv⟩ :=
      exists_captured_boundary_target_chart e he hinj hemb γ hsmooth hregular targetPuncture
  rw [htarget0] at hEc hcapture
  obtain ⟨R0, hR0, hRπ, henergy⟩ :=
    exists_boundary_half_cone_energy_comparison_uniform g he hinj hemb compact hγ F hmin
  let q0 : LoopCircle := ⟨Complex.orthonormalBasisOneI.repr p0, by
    rw [LinearIsometryEquiv.norm_map, hp0]⟩
  let J := fun z : LoopCircle × ℝ => boundaryCirclePoint
    (p := Complex.orthonormalBasisOneI.repr.symm (z.1 : LoopPlane))
    (by rw [LinearIsometryEquiv.norm_map]; exact z.1.property) z.2
  have hJ : Continuous J := boundaryCirclePoint_joint_continuous
  have hJ0 : J (q0, 0) = boundaryCirclePoint hp0 0 := by
    apply Subtype.ext
    simp only [J, q0, boundaryCirclePoint, LinearIsometryEquiv.symm_apply_apply]
  have hbeta : Continuous (fun z => F.parameter (J z)) := F.parameter.continuous.comp hJ
  have hdist : Continuous (fun z => dist (e (γ (F.parameter (J z)))) (e (γ b0))) :=
    ((he.continuous.comp hγ).comp hbeta).dist continuous_const
  have hsourceNear : ∀ᶠ z in 𝓝 (q0, (0 : ℝ)), F.parameter (J z) ∈ E.source :=
    hbeta.continuousAt.preimage_mem_nhds (E.open_source.mem_nhds (by simpa only [hJ0] using hEc))
  have hnear : ∀ᶠ z in 𝓝 (q0, (0 : ℝ)), F.parameter (J z) ∈ E.source ∧
      dist (e (γ (F.parameter (J z)))) (e (γ b0)) < δ0 / 2 :=
    hsourceNear.and
      (hdist.continuousAt.eventually (Iio_mem_nhds (by
        simpa only [hJ0, b0, dist_self] using half_pos hδ)))
  obtain ⟨r0, hr0, hrnear⟩ := Metric.mem_nhds_iff.mp hnear
  let R := min R0 (r0 / 2)
  have hR : 0 < R := lt_min hR0 (half_pos hr0)
  obtain ⟨c, C, hc, hC, hmetric⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let B := (C * K ^ 2 / 4) * (1 + Real.pi ^ 2) * K ^ 2
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨R, δ0 / 2, B, r0 / 2, hR, half_pos hδ, hB, half_pos hr0, ?_⟩
  intro p hp hpp0 r hr hrR
  dsimp only
  intro hOldU hOldD V W hV htarget hV0 hVπ hW hinc hosc hGreen
  let sourcePuncture : LoopCircle := ⟨-Complex.orthonormalBasisOneI.repr p, by
    rw [norm_neg, LinearIsometryEquiv.norm_map, hp]⟩
  have hArc (t : ℝ) : boundaryCirclePoint hp t = puncturedArc sourcePuncture t :=
    boundaryCirclePoint_eq_puncturedArc hp t
  have hsmall (t : ℝ) (ht : |t| ≤ R) :
      F.parameter (boundaryCirclePoint hp t) ∈ E.source ∧
        dist (e (γ (F.parameter (boundaryCirclePoint hp t)))) (e (γ b0)) < δ0 / 2 := by
    let q : LoopCircle := ⟨Complex.orthonormalBasisOneI.repr p, by
      rw [LinearIsometryEquiv.norm_map, hp]⟩
    have hdistq : dist q q0 = dist p p0 :=
      Complex.orthonormalBasisOneI.repr.dist_map p p0
    have hqt : (q, t) ∈ ball (q0, (0 : ℝ)) r0 := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, hdistq, Real.dist_eq, sub_zero]
      exact ⟨hpp0.trans (half_lt_self hr0),
        ht.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr0))⟩
    have hJq : J (q, t) = boundaryCirclePoint hp t := by
      apply Subtype.ext
      simp only [J, q, boundaryCirclePoint, LinearIsometryEquiv.symm_apply_apply]
    simpa only [mem_ofPred_eq, hJq] using hrnear hqt
  let v := H ∘ V
  let d := fun θ => fderiv ℝ H (V θ) (W θ)
  have hrR0 : r ≤ R0 := hrR.trans (min_le_left _ _)
  have hplus := hsmall r (by rwa [abs_of_pos hr])
  have hminus := hsmall (-r) (by rwa [abs_neg, abs_of_pos hr])
  have hcap (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
      ‖v θ‖ < ρ / 4 ∧ e (A (v θ)) = V θ := by
    obtain ⟨q, hq⟩ := htarget hθ
    have hclose : dist (e q) (e (γ b0)) < δ0 := by
      rw [hq]
      have hh := dist_triangle (V θ) (V 0) (e (γ b0))
      have hfirst : dist (V θ) (V 0) < δ0 / 2 := by
        rw [dist_eq_norm]
        exact hosc θ hθ
      have hlast : dist (V 0) (e (γ b0)) < δ0 / 2 := by rw [hV0]; exact hplus.2
      linarith only [hh, hfirst, hlast]
    have hh := hcapture q hclose
    exact ⟨by simpa only [v, Function.comp_apply, hq] using hh.1,
      by simpa only [v, Function.comp_apply, hq] using congrArg e hh.2⟩
  obtain ⟨hv, hd, hvi, hde⟩ := semicircle_coordinate_data H hH hLip hHD hV hW hinc
  have hvc : ContinuousOn v (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hv.continuousOn
  have hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 ρ) := by
    intro θ hθ
    rw [mem_closedBall_zero_iff]
    linarith [(hcap θ hθ).1]
  have hg : ContDiffOn ℝ 1 (e ∘ A) (ball 0 (2 * ρ)) :=
    contMDiffOn_iff_contDiffOn.mp ((he.of_le (by simp)).comp_contMDiffOn hA)
  have hv0 : v 0 = E (F.parameter (boundaryCirclePoint hp r)) •
      EuclideanSpace.basisFun (Fin 3) ℝ j := by
    change H (V 0) = _
    rw [hV0]
    exact haxis _ hplus.1
  have hvπ : v Real.pi = E (F.parameter (boundaryCirclePoint hp (-r))) •
      EuclideanSpace.basisFun (Fin 3) ℝ j := by
    change H (V Real.pi) = _
    rw [hVπ]
    exact haxis _ hminus.1
  obtain ⟨beta, hbeta, hbetaV, hbetaOut⟩ :=
    weak_parameter_closed_arc_replacement sourcePuncture hr (hrR0.trans_lt hRπ) E
      hconv F.parameter F.weakly_monotone (by
        intro t ht
        change F.parameter (puncturedArc sourcePuncture t) ∈ E.source
        rw [← hArc t]
        exact (hsmall t ((abs_le.mpr ht).trans hrR)).1)
  have hbetaV' (s : ℝ) (hs : s ∈ Icc (-r) r) : beta (boundaryCirclePoint hp s) =
      E.symm (AffineMap.lineMap (E (F.parameter (boundaryCirclePoint hp (-r))))
        (E (F.parameter (boundaryCirclePoint hp r))) ((s + r) / (2 * r))) := by
    simpa only [← hArc] using hbetaV s hs
  have hdiam (s : ℝ) (hs : s ∈ Icc (-r) r) :
      A (halfConeDiameter r (v 0) (v Real.pi) s) = γ (beta (boundaryCirclePoint hp s)) := by
    let t := AffineMap.lineMap (E (F.parameter (boundaryCirclePoint hp (-r))))
      (E (F.parameter (boundaryCirclePoint hp r))) ((s + r) / (2 * r))
    have ht : t ∈ E.target := hconv.lineMap_mem (E.map_source hminus.1) (E.map_source hplus.1)
      ⟨div_nonneg (by linarith [hs.1]) (by linarith),
        (div_le_one (by linarith : 0 < 2 * r)).mpr (by linarith [hs.2])⟩
    have hline : halfConeDiameter r (v 0) (v Real.pi) s =
        t • EuclideanSpace.basisFun (Fin 3) ℝ j := by
      rw [halfConeDiameter, hv0, hvπ]
      simp only [t, AffineMap.lineMap_apply_module, smul_smul, add_smul]
      module
    rw [hline, haxisInv t ht, hbetaV' s hs]
  have hmatch (z : LoopCircle) (hz : z ∉ boundaryCirclePoint hp '' Icc (-r) r) :
      beta z = F.parameter z := by
    apply hbetaOut z
    simpa only [← show boundaryCirclePoint hp = puncturedArc sourcePuncture from funext hArc]
      using hz
  have hcomparison := henergy hp r hr hrR0 A v d ρ K hρ hK.le hv hg hvb hd hvi hAD
    hOldU hOldD beta hbeta hmatch hdiam (by
      intro test i j
      rw [hGreen test i j]
      congr 2
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      rw [(hcap θ (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)).2])
  let m := (1 / 2 : ℝ) • (v 0 + v Real.pi)
  let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
  have hm : m ∈ closedBall 0 ρ := by
    simpa only [m, smul_add] using (convex_closedBall (0 : LoopAmbient) ρ)
      (hvb ⟨le_rfl, Real.pi_pos.le⟩) (hvb ⟨Real.pi_pos.le, le_rfl⟩)
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  have hLp := halfCone_memLp hr hρ hK.le hvc hg hm hvb hd hAD (0 : LoopPlane)
  have hEI : IntegrableOn (m65EmbeddedEnergyDensity g e (coneDiskMap A r m v 0)
      (coneDiskField (e ∘ A) r m v d 0)) S :=
    m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact hLp.1.1 hLp.2
  have hder := halfCone_derivativeEnergy_le hr hρ hK.le hvc hg hm hvb hd hAD (0 : LoopPlane)
  have heBound : (∫ z in S, m65EmbeddedEnergyDensity g e (coneDiskMap A r m v 0)
      (coneDiskField (e ∘ A) r m v d 0) z) ≤
      (C / 2) * ∫ z in S, ∑ i : Fin 2, ‖coneDiskField (e ∘ A) r m v d 0 i z‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hEI (hder.1.const_mul _)
    exact ae_of_all _ fun z =>
      (m65EmbeddedEnergyDensity_bounds g e hmetric (coneDiskMap A r m v 0)
        (coneDiskField (e ∘ A) r m v d 0) z).2
  have hmid := midpoint_angular_energy_le hvc hd hvi
  calc
    _ ≤ ∫ z in S, m65EmbeddedEnergyDensity g e (coneDiskMap A r m v 0)
        (coneDiskField (e ∘ A) r m v d 0) z := hcomparison
    _ ≤ (C / 2) * ((K ^ 2 / 2) *
        ∫ θ in Icc (0 : ℝ) Real.pi, (‖v θ - m‖ ^ 2 + ‖d θ‖ ^ 2)) :=
      heBound.trans (mul_le_mul_of_nonneg_left hder.2 (by positivity))
    _ ≤ (C / 2) * ((K ^ 2 / 2) *
        ((1 + Real.pi ^ 2) * ∫ θ in Icc (0 : ℝ) Real.pi, ‖d θ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmid (by positivity)) (by positivity)
    _ ≤ (C / 2) * ((K ^ 2 / 2) *
        ((1 + Real.pi ^ 2) * (K ^ 2 * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hde (by positivity)) (by positivity)) (by positivity)
    _ = _ := by dsimp only [B]; ring

theorem boundary_small_semicircle_comparison {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ q, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e q))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ R δ B : ℝ, 0 < R ∧ 0 < δ ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      MemLp (fun z => e (F.value (P z))) 2 (volume.restrict S) →
      (∀ i, MemLp (weakDiskBoundaryField F p i) 2 (volume.restrict S)) →
      ∀ V W : ℝ → EuclideanSpace ℝ (Fin N),
        AbsolutelyContinuousOnInterval V 0 Real.pi →
        MapsTo V (Icc (0 : ℝ) Real.pi) (range e) →
        V 0 = e (γ (F.parameter (boundaryCirclePoint hp r))) →
        V Real.pi = e (γ (F.parameter (boundaryCirclePoint hp (-r)))) →
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) Real.pi)) →
        (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
          V t - V s = ∫ θ in s..t, W θ) →
        (∀ θ ∈ Icc (0 : ℝ) Real.pi, ‖V θ - V 0‖ < δ) →
        (∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N),
          (∫ z in S, weakDiskBoundaryField F p i z j * test z + e (F.value (P z)) j *
            fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
              r * (∫ θ in (0 : ℝ)..Real.pi,
                V θ j * test (r • Proofs.M58.angularPoint θ) * Proofs.M58.angularPoint θ i) -
              (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                ∫ s in (-r)..r, e (γ (F.parameter (boundaryCirclePoint hp s))) j *
                  test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0)) →
        (∫ z in S, m65EmbeddedEnergyDensity g e (fun z => F.value (P z))
          (weakDiskBoundaryField F p) z) ≤ B * ∫ θ in Icc (0 : ℝ) Real.pi, ‖W θ‖ ^ 2 := by
  obtain ⟨R, δ, B, η, hR, hδ, hB, hη, h⟩ :=
    boundary_small_semicircle_comparison_uniform g he hinj hemb compact hγ hsmooth hregular
      F hmin hp
  exact ⟨R, δ, B, hR, hδ, hB, h hp (by simpa only [dist_self] using hη)⟩

end PoincareConjecture.M65Boundary
