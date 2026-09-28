import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Parametrization
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPostcompose
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

private theorem spatial_jet_convergence
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {A : ℕ → ℝ × E → B} {A₀ : ℝ × E → B} (t : ℝ) (r : ℕ) {K : Set E}
    (hjet : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (A k))
      (iteratedFDeriv ℝ r A₀) atTop ((fun x => (t, x)) '' K))
    (hreg : ∀ᶠ k in atTop, ∀ x ∈ K, ContDiffAt ℝ ∞ (A k) (t, x))
    (hreg₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ A₀ (t, x)) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (fun x => A k (t, x)))
      (iteratedFDeriv ℝ r (fun x => A₀ (t, x))) atTop K := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := B) (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)
  have hrestricted := (hjet.comp (fun x => (t, x))).mono
    (fun x hx => mem_image_of_mem (fun y => (t, y)) hx)
  have hproject := P.uniformContinuous.comp_tendstoUniformlyOn hrestricted
  apply (hproject.congr ?_).congr_right ?_
  · filter_upwards [hreg] with k hk x hx
    apply ContinuousMultilinearMap.ext
    intro v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _ (hk x hx) r v).symm
  · intro x hx
    apply ContinuousMultilinearMap.ext
    intro v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _ (hreg₀ x hx) r v).symm



theorem tendstoUniformlyOn_parametrized_spatial_jets
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    {t : ℝ} (ht : t ∈ Ioo a b) (r : ℕ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        (((S.flow (G.subsequence k)).metricAt t).pullbackCoefficients
          (fun y => ((G.embedding k).toFun (0, f y)).2)))
      (iteratedFDeriv ℝ r ((G.limitFlow.metricAt t).pullbackCoefficients f)) atTop K := by
  let e : EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin n) := fun x => (t, x)
  have he : Continuous e := continuous_const.prodMk continuous_id
  have hjet := G.tendstoUniformlyOn_parametrized_spacetime_jets hzero hU hf r
    (hK.image he) (by rintro _ ⟨x, hx, rfl⟩; exact ⟨ht, hKU hx⟩)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU))
  apply spatial_jet_convergence t r hjet
  · filter_upwards [eventually_ge_atTop j] with k hk x hx
    have hxj := G.exhaustion_monotone hk (hj (mem_image_of_mem f hx))
    have hmap := ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k)
      hzero hxj).comp x (hf.contMDiffAt (hU.mem_nhds (hKU hx)))
    exact (S.flow (G.subsequence k)).flow.smooth.contDiffAt_spacetime_pullbackCoefficients
      isOpen_Ioo hmap ht
  · intro x hx
    exact G.limitFlow.flow.smooth.contDiffAt_spacetime_pullbackCoefficients
      isOpen_Ioo (hf.contMDiffAt (hU.mem_nhds (hKU hx))) ht



theorem locally_eventually_smooth_parametrized_coefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) (t : ℝ) :
    ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (((S.flow (G.subsequence k)).metricAt t).pullbackCoefficients
          (fun y => ((G.embedding k).toFun (0, f y)).2)) W := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hx)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU))
  refine ⟨interior K, isOpen_interior, hxK (mem_singleton _), interior_subset.trans hKU, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk y hy
  have hym := G.exhaustion_monotone hk (hj (mem_image_of_mem f (interior_subset hy)))
  have hmap := ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hym).comp y
    (hf.contMDiffAt (hU.mem_nhds (hKU (interior_subset hy))))
  exact (((S.flow (G.subsequence k)).metricAt t).contDiffAt_pullbackCoefficients hmap).contDiffWithinAt

end PoincareConjecture.PointedGeometricConvergence

namespace PoincareConjecture

private theorem mfderiv_comp_linearEquiv_apply
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : E' ≃L[ℝ] E) (f : E → M) (x v : E') :
    mfderiv 𝓘(ℝ, E') (𝓡 n) (f ∘ e) x v =
      mfderiv 𝓘(ℝ, E) (𝓡 n) f (e x) (e v) := by
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (e x)
  · rw [mfderiv_comp x hf e.mdifferentiableAt, ContinuousLinearEquiv.mfderiv_eq]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, E') (𝓡 n) (f ∘ e) x := by
      intro hc
      have hc' : MDifferentiableAt 𝓘(ℝ, E') (𝓡 n) (f ∘ e) (e.symm (e x)) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hc
      have hback := hc'.comp (e x) e.symm.mdifferentiableAt
      apply hf
      simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

namespace PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space



theorem smooth_convergence_parametrized_inner
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {U : Set E} (hU : IsOpen U) {f : E → G.limitCarrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ f U)
    {t : ℝ} (ht : t ∈ Ioo a b) (v w : E) :
    let A : ℕ → E → ℝ := fun k x =>
      ((S.flow (G.subsequence k)).metricAt t).inner
        (((G.embedding k).toFun (0, f x)).2)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (fun y => ((G.embedding k).toFun (0, f y)).2) x v)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (fun y => ((G.embedding k).toFun (0, f y)).2) x w)
    let A₀ : E → ℝ := fun x => (G.limitFlow.metricAt t).inner (f x)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f x v) (mfderiv 𝓘(ℝ, E) (𝓡 n) f x w)
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (iteratedFDeriv ℝ m A₀) atTop K := by
  let V := e.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have hparam : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f ∘ e.symm) V :=
    hf.comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  let L := (ContinuousLinearMap.apply ℝ ℝ (e w)).comp
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (e v))
  have hlim : ContDiffOn ℝ ∞ ((G.limitFlow.metricAt t).pullbackCoefficients (f ∘ e.symm)) V :=
    fun x hx => ((G.limitFlow.metricAt t).contDiffAt_pullbackCoefficients
      (hparam.contMDiffAt (hV.mem_nhds hx))).contDiffWithinAt
  obtain ⟨hloc, hjet⟩ :=
    Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp L hV hlim
      (fun x hx =>
        let ⟨W, hW, hxW, _, hks⟩ :=
          G.locally_eventually_smooth_parametrized_coefficients hzero hV hparam t x hx
        ⟨W, hW, hxW, hks⟩)
      (fun m K hK hKV =>
        G.tendstoUniformlyOn_parametrized_spatial_jets hzero hV hparam ht m hK hKV)
  have hloc' := Poincare.Analysis.Calculus.locally_eventually_smooth_comp_continuousLinearEquiv
    e hloc
  have hjet' := Poincare.Analysis.Calculus.compact_jet_convergence_comp_continuousLinearEquiv
    e hjet
  have heq {D : FlowCarrier n} (g : RiemannianMetric n D.carrier)
      (F : E → D.carrier) (x : E) :
      L (g.pullbackCoefficients (fun y => F (e.symm y)) (e x)) =
        g.inner (F x) (mfderiv 𝓘(ℝ, E) (𝓡 n) F x v)
          (mfderiv 𝓘(ℝ, E) (𝓡 n) F x w) := by
    change L (g.pullbackCoefficients (F ∘ e.symm) (e x)) = _
    dsimp only [TangentSpace] at *
    simp only [Function.comp_apply, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply]
    erw [mfderiv_comp_linearEquiv_apply, mfderiv_comp_linearEquiv_apply]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact congrArg (fun z => g.inner (F z)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) F z v) (mfderiv 𝓘(ℝ, E) (𝓡 n) F z w))
      (e.symm_apply_apply x)
  have hs (k : ℕ) :
      ((L ∘ ((S.flow (G.subsequence k)).metricAt t).pullbackCoefficients
        (fun y => ((G.embedding k).toFun (0, (f ∘ e.symm) y)).2)) ∘ e) =
      (fun x => ((S.flow (G.subsequence k)).metricAt t).inner
        (((G.embedding k).toFun (0, f x)).2)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (fun y => ((G.embedding k).toFun (0, f y)).2) x v)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) (fun y => ((G.embedding k).toFun (0, f y)).2) x w)) :=
    funext (heq ((S.flow (G.subsequence k)).metricAt t)
      (fun y => ((G.embedding k).toFun (0, f y)).2))
  have hs₀ : ((L ∘ (G.limitFlow.metricAt t).pullbackCoefficients (f ∘ e.symm)) ∘ e) =
      (fun x => (G.limitFlow.metricAt t).inner (f x)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) f x v) (mfderiv 𝓘(ℝ, E) (𝓡 n) f x w)) :=
    funext (heq (G.limitFlow.metricAt t) f)
  simp only [hs, hs₀] at hloc' hjet'
  have hVback : e ⁻¹' V = U := by ext x; simp [V]
  rw [hVback] at hloc' hjet'
  exact ⟨hloc', hjet'⟩



theorem smooth_convergence_parametrized_coefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {U : Set E} (hU : IsOpen U) {f : E → G.limitCarrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ f U)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    let A : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun k =>
      ((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients
        (fun y => ((G.embedding k).toFun (0, f y)).2)
    let A₀ := (G.limitFlow.metricAt t).parametrizedCoefficients f
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (iteratedFDeriv ℝ m A₀) atTop K := by
  let V := e.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have hparam : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f ∘ e.symm) V :=
    hf.comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] ℝ) := (e.symm.arrowCongr
    (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).toContinuousLinearMap
  have hlim : ContDiffOn ℝ ∞ ((G.limitFlow.metricAt t).pullbackCoefficients (f ∘ e.symm)) V :=
    fun x hx => ((G.limitFlow.metricAt t).contDiffAt_pullbackCoefficients
      (hparam.contMDiffAt (hV.mem_nhds hx))).contDiffWithinAt
  obtain ⟨hloc, hjet⟩ :=
    Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp (G := E →L[ℝ] E →L[ℝ] ℝ) L hV hlim
      (fun x hx =>
        let ⟨W, hW, hxW, _, hks⟩ :=
          G.locally_eventually_smooth_parametrized_coefficients hzero hV hparam t x hx
        ⟨W, hW, hxW, hks⟩)
      (fun m K hK hKV =>
        G.tendstoUniformlyOn_parametrized_spatial_jets hzero hV hparam ht m hK hKV)
  have hloc' := Poincare.Analysis.Calculus.locally_eventually_smooth_comp_continuousLinearEquiv
    e hloc
  have hjet' := Poincare.Analysis.Calculus.compact_jet_convergence_comp_continuousLinearEquiv
    e hjet
  have heq {D : FlowCarrier n} (g : RiemannianMetric n D.carrier)
      (F : E → D.carrier) (x : E) :
      L (g.pullbackCoefficients (F ∘ e.symm) (e x)) =
        g.parametrizedCoefficients F x := by
    ext v w
    change g.pullbackCoefficients (F ∘ e.symm) (e x) (e v) (e w) =
      g.parametrizedCoefficients F x v w
    rw [RiemannianMetric.parametrizedCoefficients_apply]
    simp only [RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply]
    erw [mfderiv_comp_linearEquiv_apply, mfderiv_comp_linearEquiv_apply]
    simp only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
    exact congrArg (fun z => g.inner (F z)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) F z v) (mfderiv 𝓘(ℝ, E) (𝓡 n) F z w))
      (e.symm_apply_apply x)
  have hs (k : ℕ) :
      ((L ∘ ((S.flow (G.subsequence k)).metricAt t).pullbackCoefficients
        (fun y => ((G.embedding k).toFun (0, (f ∘ e.symm) y)).2)) ∘ e) =
        ((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients
          (fun y => ((G.embedding k).toFun (0, f y)).2) :=
    funext (heq ((S.flow (G.subsequence k)).metricAt t)
      (fun y => ((G.embedding k).toFun (0, f y)).2))
  have hs₀ : ((L ∘ (G.limitFlow.metricAt t).pullbackCoefficients (f ∘ e.symm)) ∘ e) =
      (G.limitFlow.metricAt t).parametrizedCoefficients f :=
    funext (heq (G.limitFlow.metricAt t) f)
  simp only [hs, hs₀] at hloc' hjet'
  have hVback : e ⁻¹' V = U := by ext x; simp [V]
  rw [hVback] at hloc' hjet'
  exact ⟨hloc', hjet'⟩

end PointedGeometricConvergence
end PoincareConjecture
