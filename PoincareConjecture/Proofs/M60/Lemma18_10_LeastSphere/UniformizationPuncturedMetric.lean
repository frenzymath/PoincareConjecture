import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationLogarithmicPuncture
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationCompactification











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem exists_sphere_logarithmic_flattening
    (q : RiemannianMetric 2 UnitTwoSphere) (p : UnitTwoSphere) :
    ∃ (g : RiemannianMetric 2 UnitTwoSphere) (F : UnitTwoSphere → ℝ),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ x v w, g.inner x v w = Real.exp (-2 * F x) * q.inner x v w) ∧
      ∃ (D : LeviCivitaData g) (W : UnitTwoSphere → ℝ),
        (∀ x ≠ p, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ W x) ∧
        (∀ x ≠ p, D.laplacian W x = -D.scalarCurvature x / 2) ∧
        ∃ (e : OpenPartialHomeomorph Plane UnitTwoSphere) (a : Plane)
          (J : Plane → ℝ),
          a ∈ e.source ∧ e a = p ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          (∀ x ∈ e.source, ∀ v w, g.pullbackCoefficients e x v w = inner ℝ v w) ∧
          ContDiffOn ℝ ∞ J e.source ∧
          (∀ x ∈ e.source, x ≠ a → W (e x) = 2 * Real.log ‖x - a‖ + J x) := by
  let : PreconnectedSpace UnitTwoSphere := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num [LoopAmbient]) (0 : LoopAmbient) 1)
  obtain ⟨Dq⟩ := m01_exists_leviCivitaData q
  obtain ⟨F, hF, e, a, U, hU, ha, hUs, hap, he, hei, hmetric⟩ :=
    exists_conformal_euclidean_near_point q Dq p
  let g := M36.positiveScaling q (fun y => Real.exp (-2 * F y))
    (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  let E := e.restr U
  have hEs : E.source = e.source ∩ U := by simp [E, hU.interior_eq]
  have haE : a ∈ E.source := by rw [hEs]; exact ⟨hUs ha, ha⟩
  have hE : ContMDiffOn (𝓡 2) (𝓡 2) ∞ E E.source := by
    exact he.mono (by rw [hEs]; exact inter_subset_left)
  have hEi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ E.symm E.target := by
    exact hei.mono (fun _ hx => hx.1)
  have hEg (x : Plane) (hx : x ∈ E.source) (v w : Plane) :
      g.pullbackCoefficients E x v w = inner ℝ v w :=
    hmetric x ((hEs ▸ hx).2) v w
  obtain ⟨V, C, hC, hCint, hV, hVlap, J, hJ, hVlog⟩ :=
    exists_flat_chart_logarithmic_puncture g D E hE hEi hEg a haE
  let f : UnitTwoSphere → ℝ := fun x => -D.scalarCurvature x / 2 - 2 * C x
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (D.contMDiff_scalarCurvature.neg.div_const 2).sub (contMDiff_const.mul hC)
  have hRi : Integrable D.scalarCurvature g.volumeMeasure :=
    D.contMDiff_scalarCurvature.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCi : Integrable C g.volumeMeasure :=
    hC.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : (∫ x, f x ∂g.volumeMeasure) = 0 := by
    dsimp only [f]
    rw [integral_sub (f := fun x => -D.scalarCurvature x / 2)
      (g := fun x => 2 * C x) (hRi.neg.div_const 2) (hCi.const_mul 2),
      integral_div, integral_neg, integral_const_mul,
      integral_scalarCurvature_sphere g D, hCint]
    ring
  obtain ⟨A, hA, hAlap⟩ := exists_smooth_poisson_closed_surface D f hf hmean
  let W : UnitTwoSphere → ℝ := fun x => A x + 2 * V x
  have hWp (x : UnitTwoSphere) (hx : x ≠ p) :
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ W x :=
    hA.contMDiffAt.add (contMDiffAt_const.mul (hV x (by simpa [E, hap] using hx)))
  have hWlap (x : UnitTwoSphere) (hx : x ≠ p) :
      D.laplacian W x = -D.scalarCurvature x / 2 := by
    obtain ⟨chi, -, hchi⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) x).mem_iff.mp
      (isOpen_compl_singleton.mem_nhds hx)
    let V0 : UnitTwoSphere → ℝ := fun y => chi y * V y
    have hV0 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ V0 := by
      apply contMDiff_of_tsupport
      intro y hy
      exact chi.contMDiffAt.mul (hV y
        (by simpa [E, hap] using hchi (tsupport_mul_subset_left hy)))
    have hVeq : V0 =ᶠ[𝓝 x] V := by
      filter_upwards [chi.eventuallyEq_one] with y hy
      simp [V0, hy]
    have heq : (fun y => A y + 2 * V0 y) =ᶠ[𝓝 x] W := by
      filter_upwards [hVeq] with y hy
      change A y + 2 * V0 y = A y + 2 * V y
      rw [hy]
    rw [← D.laplacian_eq_of_eventuallyEq heq,
      D.laplacian_add (h := fun y => 2 * V0 y) hA (contMDiff_const.mul hV0),
      D.laplacian_const_mul,
      D.laplacian_eq_of_eventuallyEq hVeq, hAlap x,
      hVlap x (by simpa [E, hap] using hx)]
    dsimp [f]
    ring
  refine ⟨g, F, hF, fun _ _ _ => rfl, D, W, hWp, hWlap, E, a,
    fun x => A (E x) + 2 * J (x - a), haE, hap, hE, hEi, hEg, ?_, ?_⟩
  · apply contMDiffOn_iff_contDiffOn.mp
    exact (hA.comp_contMDiffOn hE).add
      (contMDiffOn_const.mul ((contMDiff_iff_contDiff.mpr hJ).comp_contMDiffOn
        (contMDiff_id.sub contMDiff_const).contMDiffOn))
  · intro x hx hxa
    change A (E x) + 2 * V (E x) = _
    rw [hVlog x hx hxa]
    ring

attribute [-instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem exists_flat_punctured_metric
    (g : RiemannianMetric 2 UnitTwoSphere) (D : LeviCivitaData g)
    (W : UnitTwoSphere → ℝ)
    (hW : ∀ x ≠ m60SpherePole, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ W x)
    (hlap : ∀ x ≠ m60SpherePole, D.laplacian W x = -D.scalarCurvature x / 2) :
    ∃ (G : RiemannianMetric 2 Plane) (DG : LeviCivitaData G),
      (∀ x, DG.scalarCurvature x = 0) ∧
      ∀ x v w, G.inner x v w = Real.exp (-2 * W (m60SphereParameter x)) *
        g.inner (m60SphereParameter x)
          (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x v)
          (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x w) := by
  let Q : RiemannianMetric 2 Plane := RiemannianMetric.Induced.pullbackMetric g
    m60SphereParameter m60SphereParameter_contMDiff
      (fun x => (m60SphereParameter_mfderiv_isInvertible x).injective)
  obtain ⟨DQ⟩ := m01_exists_leviCivitaData Q
  have hp (x : Plane) : m60SphereParameter x ≠ m60SpherePole := by
    have h := m60SphereChart.symm.map_source (show x ∈ m60SphereChart.target by
      simp [m60SphereChart])
    simpa [m60SphereChart, m60SphereParameter] using h
  have hW0 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (W ∘ m60SphereParameter) := fun x =>
    (hW _ (hp x)).comp x m60SphereParameter_contMDiff.contMDiffAt
  let G := M36.positiveScaling Q (fun x => Real.exp (-2 * W (m60SphereParameter x)))
    (M36.contMDiff_exp_neg_two hW0) (fun _ => Real.exp_pos _)
  obtain ⟨DG⟩ := m01_exists_leviCivitaData G
  have hmetric (x : Plane) (v w : Plane) : Q.inner x v w =
      g.inner (m60SphereParameter x)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x v)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x w) := rfl
  have hR (x : Plane) : DQ.scalarCurvature x = D.scalarCurvature (m60SphereParameter x) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : Plane → Type _) :=
      ⟨Q.toRiemannianMetric⟩
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
      change Module.finrank ℝ Plane = 2
      simp [Plane]
    let b := (Q.orthonormalBasis x).reindex (finCongr hdim)
    have hb (i j : Fin 2) : Q.inner x (b i) (b j) = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    rw [DQ.scalarCurvature_eq_twice_curvatureTensor x b,
      DQ.curvatureTensor_eq_pullback_euclidean D m60SphereParameter_contMDiff.contMDiffAt
        (Eventually.of_forall m60SphereParameter_mfderiv_isInvertible)
        (Eventually.of_forall hmetric), D.curvatureTensor_eq_half_scalarCurvature]
    simp only [← hmetric, hb]
    norm_num
    ring
  have hL (x : Plane) : DQ.laplacian (W ∘ m60SphereParameter) x =
      -DQ.scalarCurvature x / 2 := by
    rw [DQ.laplacian_comp_of_metric_pullback D
      m60SphereParameter_contMDiff.contMDiffAt
      (Eventually.of_forall m60SphereParameter_mfderiv_isInvertible)
      (Eventually.of_forall hmetric) (hW _ (hp x)), hlap _ (hp x), hR]
  refine ⟨G, DG, fun x => ?_, fun _ _ _ => rfl⟩
  rw [scalarCurvature_conformal_surface Q DQ _ hW0 DG, hL]
  ring



theorem exists_smooth_puncture_exponential
    (p : UnitTwoSphere) (W : UnitTwoSphere → ℝ)
    (hW : ∀ x ≠ p, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ W x)
    (e : OpenPartialHomeomorph Plane UnitTwoSphere) (a : Plane)
    (ha : a ∈ e.source) (hap : e a = p)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (J : Plane → ℝ) (hJ : ContDiffOn ℝ ∞ J e.source)
    (hlog : ∀ x ∈ e.source, x ≠ a → W (e x) = 2 * Real.log ‖x - a‖ + J x) :
    ∃ A : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A ∧
      A p = 0 ∧ ∀ x ≠ p, A x = Real.exp (W x) := by
  classical
  let A : UnitTwoSphere → ℝ := fun x => if x = p then 0 else Real.exp (W x)
  let H : Plane → ℝ := fun x => ‖x - a‖ ^ 2 * Real.exp (J x)
  have hAE (x : Plane) (hx : x ∈ e.source) : A (e x) = H x := by
    by_cases hxa : x = a
    · subst x
      simp [A, H, hap]
    · have hxp : e x ≠ p := by
        intro h
        exact hxa (e.injOn hx ha (h.trans hap.symm))
      rw [show A (e x) = Real.exp (W (e x)) by simp [A, hxp], hlog x hx hxa]
      have hn : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxa)
      rw [Real.exp_add, show 2 * Real.log ‖x - a‖ =
        Real.log ‖x - a‖ + Real.log ‖x - a‖ by ring,
        Real.exp_add, Real.exp_log hn]
      dsimp [H]
      ring
  refine ⟨A, ?_, by simp [A], fun x hx => by simp [A, hx]⟩
  intro x
  by_cases hxp : x = p
  · subst x
    have hp : p ∈ e.target := hap ▸ e.map_source ha
    have hpa : e.symm p = a := by rw [← hap, e.left_inv ha]
    have hH : ContDiffAt ℝ ∞ H a :=
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt.mul
        ((hJ.contDiffAt (e.open_source.mem_nhds ha)).exp)
    have hH' : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ H (e.symm p) := by
      rw [hpa]
      exact contMDiffAt_iff_contDiffAt.mpr hH
    have hs := hH'.comp p
      (hei.contMDiffAt (e.open_target.mem_nhds hp))
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hp] with y hy
    have h := hAE (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at h
    exact h
  · apply (Real.contDiff_exp.contMDiff.contMDiffAt.comp x (hW x hxp)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hxp] with y hy
    simp [A, show y ≠ p from hy]




theorem metricComplete_sphere_puncture
    (g : RiemannianMetric 2 UnitTwoSphere) (G : RiemannianMetric 2 Plane)
    (W A : UnitTwoSphere → ℝ)
    (hW : ∀ x ≠ m60SpherePole, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ W x)
    (hA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A) (hA0 : A m60SpherePole = 0)
    (hAe : ∀ x ≠ m60SpherePole, A x = Real.exp (W x))
    (hG : ∀ x v w, G.inner x v w = Real.exp (-2 * W (m60SphereParameter x)) *
      g.inner (m60SphereParameter x)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x v)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x w)) : MetricComplete G := by
  have hp (x : Plane) : m60SphereParameter x ≠ m60SpherePole := by
    have h := m60SphereChart.symm.map_source (show x ∈ m60SphereChart.target by
      simp [m60SphereChart])
    simpa [m60SphereChart, m60SphereParameter] using h
  let w := W ∘ m60SphereParameter
  have hw : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ w := fun x =>
    (hW _ (hp x)).comp x m60SphereParameter_contMDiff.contMDiffAt
  let rho : Plane → ℝ := fun x => -w x
  have hrho : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ rho := hw.neg
  have hproper (r : ℝ) : IsCompact (rho ⁻¹' Icc (-r) r) := by
    let K : Set UnitTwoSphere := {y | Real.exp (-r) ≤ A y}
    have hK : IsCompact K := (isClosed_le continuous_const hA.continuous).isCompact
    have hKs : K ⊆ m60SphereChart.source := by
      intro y hy
      have hn : y ≠ m60SpherePole := by
        intro heq
        subst y
        exact (not_le_of_gt (Real.exp_pos (-r))) (hA0 ▸ hy)
      simpa [m60SphereChart] using hn
    apply (hK.image_of_continuousOn (m60SphereChart.continuousOn.mono hKs)).of_isClosed_subset
      (isClosed_Icc.preimage hrho.continuous)
    intro x hx
    refine ⟨m60SphereParameter x, ?_, ?_⟩
    · change Real.exp (-r) ≤ A (m60SphereParameter x)
      rw [hAe _ (hp x)]
      apply Real.exp_le_exp.mpr
      have hb : -W (m60SphereParameter x) ≤ r := hx.2
      linarith
    · exact m60SphereChart.right_inv (by simp [m60SphereChart])
  obtain ⟨B, hB, hbound⟩ := g.exists_metric_derivative_bound_of_hasCompactSupport hA
    (HasCompactSupport.of_compactSpace _)
  apply metricComplete_of_proper_exhaustion G rho hrho hproper
    ⟨B + 1, by positivity⟩ (by change 0 < B + 1; positivity)
  intro x v
  let L := mfderiv (𝓡 2) (𝓡 2) m60SphereParameter x
  have hchain : mvfderiv (𝓡 2) A (m60SphereParameter x) (L v) =
      fderiv ℝ (A ∘ m60SphereParameter) x v := by
    rw [← mvfderiv_comp_apply x (hA.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _) v,
      mvfderiv, mfderiv_eq_fderiv]
    rfl
  have heq : A ∘ m60SphereParameter = fun y => Real.exp (w y) :=
    funext (fun y => hAe _ (hp y))
  have hdw := (contMDiff_iff_contDiff.mp hw).differentiable (by simp) x
  have hd : fderiv ℝ (A ∘ m60SphereParameter) x v =
      Real.exp (w x) * fderiv ℝ w x v := by
    rw [heq, hdw.hasFDerivAt.exp.fderiv]
    rfl
  have hn : G.tangentNorm x v = Real.exp (-w x) *
      g.tangentNorm (m60SphereParameter x) (L v) := by
    unfold RiemannianMetric.tangentNorm
    rw [hG]
    change Real.sqrt (Real.exp (-2 * w x) * _) = _
    rw [show Real.exp (-2 * w x) = Real.exp (-w x) ^ 2 by
      rw [show -2 * w x = -w x + -w x by ring, Real.exp_add, pow_two],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
  have hb := hbound (m60SphereParameter x) (L v)
  rw [hchain, hd, abs_mul, abs_of_pos (Real.exp_pos _)] at hb
  have hc := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-w x)).le
  have he : Real.exp (-w x) * Real.exp (w x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hc
  have hdR : mvfderiv (𝓡 2) rho x v = -fderiv ℝ w x v := by
    rw [mvfderiv, mfderiv_eq_fderiv]
    change fderiv ℝ (fun y => -w y) x v = _
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L v) hdw.hasFDerivAt.neg.fderiv
  rw [hdR, abs_neg]
  change _ ≤ (B + 1) * G.tangentNorm x v
  calc
    _ ≤ B * G.tangentNorm x v := by simpa only [hn, mul_left_comm] using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)




theorem exists_punctured_conformal_developing_map
    (q : RiemannianMetric 2 UnitTwoSphere) :
    ∃ (F : Plane ≃ₘ[ℝ] Plane) (c : Plane → ℝ),
      ContDiff ℝ ∞ c ∧ (∀ x, 0 < c x) ∧
      ∀ x v w, q.pullbackCoefficients m60SphereParameter x v w =
        c x * inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  obtain ⟨g, S, hS, hg, D, W, hW, hL, e, a, J, ha, hap, -, hei, -, hJ, hlog⟩ :=
    exists_sphere_logarithmic_flattening q m60SpherePole
  obtain ⟨G, DG, hflat, hG⟩ := exists_flat_punctured_metric g D W hW hL
  obtain ⟨A, hA, hA0, hAe⟩ :=
    exists_smooth_puncture_exponential m60SpherePole W hW e a ha hap hei J hJ hlog
  have hc := metricComplete_sphere_puncture g G W A hW hA hA0 hAe hG
  obtain ⟨F, hF⟩ := exists_diffeomorph_of_complete_flat_plane G DG hc hflat
  have hp (x : Plane) : m60SphereParameter x ≠ m60SpherePole := by
    have h := m60SphereChart.symm.map_source (show x ∈ m60SphereChart.target by
      simp [m60SphereChart])
    simpa [m60SphereChart, m60SphereParameter] using h
  let c : Plane → ℝ := fun x =>
    Real.exp (2 * (W (m60SphereParameter x) + S (m60SphereParameter x)))
  have hw : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (W ∘ m60SphereParameter) := fun x =>
    (hW _ (hp x)).comp x m60SphereParameter_contMDiff.contMDiffAt
  have hcs : ContDiff ℝ ∞ c := contMDiff_iff_contDiff.mp
    (Real.contDiff_exp.contMDiff.comp
      (contMDiff_const.mul (hw.add (hS.comp m60SphereParameter_contMDiff))))
  refine ⟨F, c, hcs, fun _ => Real.exp_pos _, fun x v w => ?_⟩
  rw [hF, hG, hg]
  have he : c x * (Real.exp (-2 * W (m60SphereParameter x)) *
      Real.exp (-2 * S (m60SphereParameter x))) = 1 := by
    dsimp only [c]
    rw [← Real.exp_add, ← Real.exp_add,
      show 2 * (W (m60SphereParameter x) + S (m60SphereParameter x)) +
        (-2 * W (m60SphereParameter x) + -2 * S (m60SphereParameter x)) = 0 by ring,
      Real.exp_zero]
  change _ = c x * (Real.exp (-2 * W (m60SphereParameter x)) *
    (Real.exp (-2 * S (m60SphereParameter x)) *
      q.pullbackCoefficients m60SphereParameter x v w))
  linear_combination -(q.pullbackCoefficients m60SphereParameter x v w) * he
end PoincareConjecture.M60

end
