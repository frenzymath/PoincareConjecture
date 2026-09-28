import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.LipschitzGreen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Regularity.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem integrable_integral_of_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {F : M → ℝ} (hs : Function.support F ⊆ e.target)
    (hcoord : IntegrableOn (fun x => F (e x) * g.pullbackVolumeDensity e x) e.source) :
    Integrable F g.volumeMeasure ∧
      (∫ x, F x ∂g.volumeMeasure) =
        ∫ x in e.source, F (e x) * g.pullbackVolumeDensity e x := by
  let μ := g.volumeMeasure.restrict e.target
  let ν := (volume.restrict e.source).withDensity
    (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  have hd : AEMeasurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
      (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable e.open_source.measurableSet
  have hν : ν.restrict e.source = ν := by
    dsimp [ν]
    rw [restrict_withDensity e.open_source.measurableSet,
      Measure.restrict_restrict e.open_source.measurableSet, inter_self]
  have hmapSymm : μ.map e.symm = ν := by
    dsimp [μ, ν]
    rw [g.map_restrict_volumeMeasure_symm e he hei,
      restrict_withDensity e.open_source.measurableSet]
  have hmeas : AEMeasurable e ν :=
    (e.continuousOn.aemeasurable e.open_source.measurableSet).mono'
      (withDensity_absolutelyContinuous _ _)
  have hmap : ν.map e = μ := by
    rw [← hmapSymm]
    rw [AEMeasurable.map_map_of_aemeasurable]
    · calc
        μ.map (e ∘ e.symm) = μ.map id := Measure.map_congr (by
          filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
          exact e.right_inv hy)
        _ = μ := Measure.map_id
    · rw [hmapSymm]
      exact hmeas
    · exact e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hemb : MeasurableEmbedding (e.source.domRestrict e) :=
    e.isOpenEmbedding_restrict.measurableEmbedding
  have hmapSub : (ν.comap (Subtype.val : e.source → EuclideanSpace ℝ (Fin n))).map
      (e.source.domRestrict e) = μ := by
    change (ν.comap (Subtype.val : e.source → EuclideanSpace ℝ (Fin n))).map
      (e ∘ Subtype.val) = μ
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · rw [map_comap_subtype_coe e.open_source.measurableSet, hν, hmap]
    · rw [map_comap_subtype_coe e.open_source.measurableSet, hν]
      exact hmeas
    · exact measurable_subtype_coe.aemeasurable
  have hweighted : Integrable (fun x => F (e x)) ν := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (by simp)).2
    have hnonneg (x) : 0 ≤ g.pullbackVolumeDensity e x := Real.sqrt_nonneg _
    simpa only [IntegrableOn, ENNReal.toReal_ofReal (hnonneg _),
      smul_eq_mul, mul_comm] using hcoord
  have hFμ : Integrable F μ := by
    rw [← hmapSub, hemb.integrable_map_iff]
    change Integrable ((fun x => F (e x)) ∘ Subtype.val)
      (ν.comap (Subtype.val : e.source → EuclideanSpace ℝ (Fin n)))
    rw [← integrableOn_iff_comap_subtypeVal e.open_source.measurableSet]
    exact hweighted.integrableOn
  constructor
  · exact (integrableOn_iff_integrable_of_support_subset hs).mp hFμ
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by by_contra hne; exact hx (hs hne))]
    change (∫ x, F x ∂μ) = _
    rw [← hmapSub, hemb.integral_map]
    change (∫ x : e.source, F (e x) ∂(ν.comap Subtype.val)) = _
    rw [integral_subtype_comap e.open_source.measurableSet (fun x => F (e x))]
    change (∫ x, F (e x) ∂ν.restrict e.source) = _
    rw [hν, integral_withDensity_eq_integral_toReal_smul₀ hd (by simp)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [ENNReal.toReal_ofReal (show 0 ≤ g.pullbackVolumeDensity e x from
        Real.sqrt_nonneg _), smul_eq_mul, mul_comm]



theorem ae_restrict_of_ae_pullback
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {P : M → Prop} (hP : ∀ᵐ x ∂volume.restrict e.source, P (e x)) :
    ∀ᵐ x ∂g.volumeMeasure.restrict e.target, P x := by
  classical
  let F : M → ℝ := fun x => if x ∈ e.target ∧ ¬P x then 1 else 0
  have hs : Function.support F ⊆ e.target := by
    intro x hx
    by_contra hnot
    exact hx (by simp [F, hnot])
  have hz : (fun x => F (e x) * g.pullbackVolumeDensity e x) =ᵐ[
      volume.restrict e.source] 0 := by
    filter_upwards [hP] with x hx
    simp [F, hx]
  have hi := g.integrable_integral_of_pullback_density e he hei hs
    (integrable_zero _ _ _ |>.congr hz.symm)
  have hzero : (∫ x, F x ∂g.volumeMeasure) = 0 := by
    rw [hi.2, integral_congr_ae hz]
    simp
  have hF := (integral_eq_zero_iff_of_nonneg
    (show 0 ≤ F from fun x => by dsimp [F]; split_ifs <;> norm_num) hi.1).mp hzero
  rw [ae_restrict_iff' e.open_target.measurableSet]
  filter_upwards [hF] with x hx hxt
  by_contra hnot
  simp [F, hxt, hnot] at hx

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in


theorem exists_lipschitz_coordinate_nhds_of_distance_lipschitz
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal) (a : M) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ U ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) U := by
  obtain ⟨C, r, hr, hball, hdist⟩ := g.exists_intrinsic_lipschitz_chart_ball a
  refine ⟨Metric.ball (extChartAt (𝓡 n) a a) r, Metric.isOpen_ball,
    Metric.mem_ball_self hr, ?_, C, ?_⟩
  · have ht : (extChartAt (𝓡 n) a).target =
        (chartAt (EuclideanSpace ℝ (Fin n)) a).target := by
      simp only [extChartAt_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ]
    exact hball.trans (le_of_eq ht)
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hreal := ENNReal.toReal_mono (by finiteness) (hdist x hx y hy)
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hreal
    exact (hLip _ _).trans hreal

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓡 n) ∞ M] in
private theorem fderiv_comp_mpullback
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {f : M → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (hf : DifferentiableAt ℝ (f ∘ e) x)
    (V : (y : M) → TangentSpace (𝓡 n) y) :
    fderiv ℝ (f ∘ e) x (mpullback (𝓡 n) (𝓡 n) e V x) =
      mvfderiv (𝓡 n) f (e x) (V (e x)) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ e) (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact hf.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hfeq : f =ᶠ[𝓝 (e x)] (f ∘ e) ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    simp only [Function.comp_apply, e.right_inv hy]
  have hfM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e x) :=
    (hf'.comp (e x) (hD.symm.mdifferentiableAt (e.map_source hx))).congr_of_eventuallyEq hfeq
  have h := congrArg (fun L => L (mpullback (𝓡 n) (𝓡 n) e V x))
    (mvfderiv_comp x hfM (hD.mdifferentiableAt hx))
  simp only [ContinuousLinearMap.comp_apply, mpullback, hinv.self_apply_inverse] at h
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at h
  convert! h using 1

private theorem linearMap_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm



theorem integral_mul_laplacian_of_lipschitzOn_chart
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hUs : U ⊆ e.source)
    {f φ : M → ℝ} (hf : Continuous f) {C : ℝ≥0}
    (hLip : LipschitzOnWith C (f ∘ e) U)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.target)
    (himage : e.symm '' tsupport φ ⊆ U) :
    Integrable (fun x => mvfderiv (𝓡 n) f x (D.gradient φ x)) g.volumeMeasure ∧
      (∫ x, f x * D.laplacian φ x ∂g.volumeMeasure) =
        -∫ x, mvfderiv (𝓡 n) f x (D.gradient φ x) ∂g.volumeMeasure := by
  classical
  let K := e.symm '' tsupport φ
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    g.pullbackVolumeDensity e x *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x) i
  let W : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i => e.source.indicator (V i)
  have hK : IsCompact K := hc.image_of_continuousOn (e.symm.continuousOn.mono hs)
  have hKs : K ⊆ e.source := himage.trans hUs
  have hWgerm (i) (x) (hx : x ∈ e.source) : W i =ᶠ[𝓝 x] V i := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  have hWs (i : Fin n) : tsupport (W i) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_cases hxs : x ∈ e.source
    · have hxφ : e x ∈ tsupport φ := by
        by_contra hnot
        apply hx
        simp [W, indicator_of_mem hxs, V, mpullback,
          D.gradient_eq_zero_of_notMem_tsupport hnot]
      exact ⟨e x, hxφ, e.left_inv hxs⟩
    · exact False.elim (hx (indicator_of_notMem hxs _))
  have hW (i : Fin n) : ContDiff ℝ ∞ (W i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.source
    · exact (D.contDiffAt_coordinateGradientFlux e he hei hx (hφ (e x)) i).congr_of_eventuallyEq
        (hWgerm i x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hKs (hWs i ht))))
  have hWc (i : Fin n) : HasCompactSupport (W i) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hWs i)
  have hp := Poincare.Analysis.WeakDerivative.integral_mul_sum_fderiv_eq_neg
    volume hU hLip (EuclideanSpace.basisFun (Fin n) ℝ) W hW hWc
    (fun i => (hWs i).trans himage)
  let H (x : EuclideanSpace ℝ (Fin n)) :=
    ∑ i, fderiv ℝ (f ∘ e) x (EuclideanSpace.basisFun (Fin n) ℝ i) * W i x
  let P (x : M) := mvfderiv (𝓡 n) f x (D.gradient φ x)
  have hHzero (x) (hx : x ∉ U) : H x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (himage (hWs i ht))), mul_zero]
  have hPzero (x) (hx : x ∉ tsupport φ) : P x = 0 := by
    simp [P, D.gradient_eq_zero_of_notMem_tsupport hx]
  have hPcoord : H =ᵐ[volume.restrict e.source]
      (fun x => P (e x) * g.pullbackVolumeDensity e x) := by
    filter_upwards [ae_restrict_of_ae
      (Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn volume hU hLip),
      ae_restrict_mem e.open_source.measurableSet] with x hdiff hx
    by_cases hxU : x ∈ U
    · change (∑ i, fderiv ℝ (f ∘ e) x (EuclideanSpace.basisFun (Fin n) ℝ i) * W i x) = _
      simp only [W, indicator_of_mem hx, P]
      rw [← fderiv_comp_mpullback e he hei hx (hdiff hxU) (D.gradient φ),
        linearMap_eq_sum_coordinates, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [V]
      ring
    · have hxφ : e x ∉ tsupport φ := by
        intro h
        exact hxU (himage ⟨e x, h, e.left_inv hx⟩)
      rw [hHzero x hxU, hPzero _ hxφ, zero_mul]
  have hPs : Function.support P ⊆ e.target := by
    intro x hx
    by_contra hnot
    exact hx (hPzero x (fun ht => hnot (hs ht)))
  obtain ⟨hPint, hPchange⟩ := g.integrable_integral_of_pullback_density e he hei hPs
    (hp.1.restrict.congr hPcoord)
  refine ⟨hPint, ?_⟩
  have hleft : (∫ x, (f ∘ e) x * ∑ i, fderiv ℝ (W i) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      ∫ x, f x * D.laplacian φ x ∂g.volumeMeasure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.source)
      (fun x hx => ?_)]
    · calc
        _ = ∫ x in e.source, (f (e x) * D.laplacian φ (e x)) *
            g.pullbackVolumeDensity e x := by
          apply setIntegral_congr_fun e.open_source.measurableSet
          intro x hx
          dsimp only
          have heq (i : Fin n) : fderiv ℝ (W i) x = fderiv ℝ (V i) x :=
            (hWgerm i x hx).fderiv_eq
          simp_rw [heq]
          rw [← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hφ (e x))]
          dsimp only [Function.comp_apply]
          ring
        _ = ∫ x in e.target, f x * D.laplacian φ x ∂g.volumeMeasure :=
          (g.integral_target_eq_integral_pullback_density e he hei
            (hf.mul (D.continuous_laplacian hφ)).continuousOn).symm
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [D.laplacian_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero])
    · have hz (i) : fderiv ℝ (W i) x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun ht => hx (hKs (hWs i (tsupport_fderiv_subset ℝ ht))))
      simp [hz]
  rw [← hleft, hp.2.2, hPchange, ← integral_congr_ae hPcoord]
  congr 1
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hHzero x (fun h => hx (hUs h)))).symm

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
private theorem laplacian_finset_sum (D : LeviCivitaData g) {ι : Type*}
    (s : Finset ι) (φ : ι → M → ℝ)
    (hφ : ∀ i ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ i)) (x : M) :
    D.laplacian (fun y => ∑ i ∈ s, φ i y) x = ∑ i ∈ s, D.laplacian (φ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact D.laplacian_eq_zero_of_notMem_tsupport (by simp)
  | @insert i s hi ih =>
      have hiφ := hφ i (Finset.mem_insert_self _ _)
      have hsφ := fun j hj => hφ j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [D.laplacian_add hiφ (ContMDiff.sum hsφ), ih hsφ]



theorem integral_mul_laplacian_of_locally_lipschitz [SigmaCompactSpace M]
    (D : LeviCivitaData g) {f φ : M → ℝ} (hf : Continuous f)
    (hlocal : ∀ a : M, ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ U ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) U)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => mvfderiv (𝓡 n) f x (D.gradient φ x)) g.volumeMeasure ∧
      (∫ x, f x * D.laplacian φ x ∂g.volumeMeasure) =
        -∫ x, mvfderiv (𝓡 n) f x (D.gradient φ x) ∂g.volumeMeasure := by
  classical
  choose O hO haO hOs C hLip using hlocal
  let U : M → Set M := fun a =>
    (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹' O a
  have hU (a) : IsOpen (U a) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) a).continuousOn.isOpen_inter_preimage
      (chartAt (EuclideanSpace ℝ (Fin n)) a).open_source (hO a)
  have hcover : (univ : Set M) ⊆ ⋃ a, U a := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source _ x, haO x⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    isClosed_univ U hU hcover
  have hfinite := ρ.locallyFinite.finite_nonempty_inter_compact hc.isCompact
  let s := hfinite.toFinset
  let ψ : M → M → ℝ := fun i x => ρ i x * φ x
  have hψ (i) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ψ i) := (ρ i).contMDiff.mul hφ
  have hψc (i) : HasCompactSupport (ψ i) := hc.mul_left
  have hψU (i) : tsupport (ψ i) ⊆ U i := tsupport_mul_subset_left.trans (hρ i)
  have hsum : φ = fun x => ∑ i ∈ s, ψ i x := by
    funext x
    have hs : Function.support (fun i => ρ i x * φ x) ⊆ s := by
      intro i hi
      apply hfinite.mem_toFinset.mpr
      refine ⟨x, (mul_ne_zero_iff.mp hi).1, subset_tsupport φ (mul_ne_zero_iff.mp hi).2⟩
    simp only [ψ]
    rw [← finsum_eq_sum_of_support_subset _ hs, ← finsum_mul,
      ρ.sum_eq_one (mem_univ x), one_mul]
  have hgreen (i : M) := D.integral_mul_laplacian_of_lipschitzOn_chart
    (chartAt (EuclideanSpace ℝ (Fin n)) i).symm
    contMDiffOn_chart_symm contMDiffOn_chart (hO i) (hOs i) hf (hLip i)
    (hψ i) (hψc i) (fun x hx => (hψU i hx).1)
    (by rintro _ ⟨x, hx, rfl⟩; exact (hψU i hx).2)
  have hpair : (fun x => mvfderiv (𝓡 n) f x (D.gradient φ x)) =
      fun x => ∑ i ∈ s, mvfderiv (𝓡 n) f x (D.gradient (ψ i) x) := by
    funext x
    rw [hsum, D.gradient_finset_sum s ψ x
      (fun i _ => (hψ i x).mdifferentiableAt (by simp)), map_sum]
  have hlap : (fun x => f x * D.laplacian φ x) =
      fun x => ∑ i ∈ s, f x * D.laplacian (ψ i) x := by
    funext x
    rw [hsum, laplacian_finset_sum D s ψ (fun i _ => hψ i) x, Finset.mul_sum]
  have hli (i : M) : Integrable (fun x => f x * D.laplacian (ψ i) x) g.volumeMeasure :=
    D.integrable_mul_laplacian_of_hasCompactSupport_right hf (hψ i) (hψc i)
  constructor
  · rw [hpair]
    exact integrable_finsetSum s (fun i _ => (hgreen i).1)
  · rw [hpair, hlap, integral_finsetSum s (fun i _ => hli i),
      integral_finsetSum s (fun i _ => (hgreen i).1), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hgreen i).2)



theorem integral_mul_laplacian_of_distance_lipschitz [PreconnectedSpace M]
    (D : LeviCivitaData g) {f φ : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => mvfderiv (𝓡 n) f x (D.gradient φ x)) g.volumeMeasure ∧
      (∫ x, f x * D.laplacian φ x ∂g.volumeMeasure) =
        -∫ x, mvfderiv (𝓡 n) f x (D.gradient φ x) ∂g.volumeMeasure := by
  have hlocal : ∀ a : M, ∃ U : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen U ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ U ∧
      U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) U :=
    g.exists_lipschitz_coordinate_nhds_of_distance_lipschitz hLip
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro a
    obtain ⟨U, hU, ha, _, C, hC⟩ := hlocal a
    have hcomp := (hC.continuousOn.continuousAt (hU.mem_nhds ha)).comp
      ((chartAt (EuclideanSpace ℝ (Fin n)) a).continuousOn.continuousAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) a).open_source.mem_nhds (mem_chart_source _ a)))
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) a).open_source.mem_nhds
      (mem_chart_source _ a)] with y hy
    simp only [Function.comp_apply, (chartAt (EuclideanSpace ℝ (Fin n)) a).left_inv hy]
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  exact D.integral_mul_laplacian_of_locally_lipschitz hf hlocal hφ hc



theorem integral_distance_mul_laplacian [PreconnectedSpace M]
    (D : LeviCivitaData g) (p : M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => mvfderiv (𝓡 n) (fun y => (g.edist p y).toReal) x
      (D.gradient φ x)) g.volumeMeasure ∧
      (∫ x, (g.edist p x).toReal * D.laplacian φ x ∂g.volumeMeasure) =
        -∫ x, mvfderiv (𝓡 n) (fun y => (g.edist p y).toReal) x
          (D.gradient φ x) ∂g.volumeMeasure :=
  D.integral_mul_laplacian_of_distance_lipschitz (g.abs_toReal_edist_sub_le p) hφ hc

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem ae_mDifferentiableAt_of_distance_lipschitz
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal) :
    ∀ᵐ x ∂g.volumeMeasure, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x := by
  classical
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  choose O hO haO hOs C hC using g.exists_lipschitz_coordinate_nhds_of_distance_lipschitz hLip
  let U : M → Set M := fun a =>
    (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹' O a
  have hU (a) : IsOpen (U a) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) a).continuousOn.isOpen_inter_preimage
      (chartAt (EuclideanSpace ℝ (Fin n)) a).open_source (hO a)
  have hcover : (univ : Set M) ⊆ ⋃ a, U a := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source _ x, haO x⟩
  have hae (a : M) : ∀ᵐ y ∂g.volumeMeasure,
      y ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y := by
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) a).symm
    have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
    have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hcoord : ∀ᵐ z ∂volume.restrict e.source,
        e z ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e z) := by
      filter_upwards [ae_restrict_of_ae
        (Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn volume (hO a) (hC a)),
        ae_restrict_mem e.open_source.measurableSet] with z hz hzs hza
      have hzO : z ∈ O a := by
        have hh := hza.2
        change e.symm (e z) ∈ O a at hh
        rwa [e.left_inv hzs] at hh
      have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ e) (e.symm (e z)) := by
        rw [e.left_inv hzs]
        exact (hz hzO).hasFDerivAt.hasMFDerivAt.mdifferentiableAt
      apply (hf'.comp (e z) (hD.symm.mdifferentiableAt (e.map_source hzs))).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds (e.map_source hzs)] with y hy
      simp only [Function.comp_apply, e.right_inv hy]
    have h := (ae_restrict_iff' e.open_target.measurableSet).mp
      (g.ae_restrict_of_ae_pullback e he hei
        (P := fun y => y ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y) hcoord)
    filter_upwards [h] with y hy hyU
    exact hy hyU.1 hyU
  obtain ⟨s, hs, hsc⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable s := hs.to_subtype
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ i : s,
      x ∈ U i → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x :=
    ae_all_iff.mpr (fun i => hae i)
  filter_upwards [hall] with x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hsc (mem_univ x))
  exact hx ⟨i, hi⟩ hxi



theorem ae_mDifferentiableAt_distance (g : RiemannianMetric n M) (p : M) :
    ∀ᵐ x ∂g.volumeMeasure,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => (g.edist p y).toReal) x :=
  g.ae_mDifferentiableAt_of_distance_lipschitz (g.abs_toReal_edist_sub_le p)

end PoincareConjecture.RiemannianMetric
