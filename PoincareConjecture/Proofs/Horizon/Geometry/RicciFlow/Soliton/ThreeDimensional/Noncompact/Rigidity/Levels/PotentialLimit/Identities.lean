import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Constancy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.SpaceTime


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem gradient_normSq_in_parametrization (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e x)
    (hi : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    {f : M → ℝ} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e x)) :
    g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) =
      fderiv ℝ (f ∘ e) x ((g.pullbackCoefficients e x).inverse (fderiv ℝ (f ∘ e) x)) := by
  let A := mfderiv (𝓡 n) (𝓡 n) e x
  let B := g.pullbackCoefficients e x
  let d := fderiv ℝ (f ∘ e) x
  have hB : B.IsInvertible := g.isInvertible_pullbackCoefficients hi.injective
  have hd : d = (mvfderiv (𝓡 n) f (e x)).comp A := by
    have h := mfderiv_comp x hf he
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hBA : B (A.inverse (D.gradient f (e x))) = d := by
    ext v
    change g.inner (e x) (A (A.inverse (D.gradient f (e x)))) (A v) = d v
    rw [hi.self_apply_inverse, D.inner_gradient, hd]
    rfl
  change g.inner (e x) (D.gradient f (e x)) (D.gradient f (e x)) = d (B.inverse d)
  rw [hB.inverse_apply_eq.mpr hBA.symm, hd]
  simp only [ContinuousLinearMap.comp_apply, D.inner_gradient]
  exact congrArg (mvfderiv (𝓡 n) f (e x)) (hi.self_apply_inverse (D.gradient f (e x))).symm

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem tendsto_clm_apply
    {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {l : Filter ι} {A : ι → V →L[ℝ] W} {a : V →L[ℝ] W}
    {v : ι → V} {w : V} (hA : Tendsto A l (𝓝 a)) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (a w)) :=
  (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hA.prodMk_nhds hv)

private theorem tendsto_fderiv_of_jet_one
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : ℕ → V → W} {b : V → W} {x : V}
    (h : Tendsto (fun k => iteratedFDeriv ℝ 1 (f k) x) atTop
      (𝓝 (iteratedFDeriv ℝ 1 b x))) :
    Tendsto (fun k => fderiv ℝ (f k) x) atTop (𝓝 (fderiv ℝ b x)) := by
  have hh := (continuousMultilinearCurryFin1 ℝ V W).continuous.continuousAt.tendsto.comp h
  have heq (a : V → W) : (continuousMultilinearCurryFin1 ℝ V W)
      (iteratedFDeriv ℝ 1 a x) = fderiv ℝ a x := by
    ext v
    simp only [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simp
  simpa only [Function.comp_def, heq] using hh

private theorem tendsto_value_of_jet_zero
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : ℕ → V → W} {b : V → W} {x : V}
    (h : Tendsto (fun k => iteratedFDeriv ℝ 0 (f k) x) atTop
      (𝓝 (iteratedFDeriv ℝ 0 b x))) :
    Tendsto (fun k => f k x) atTop (𝓝 (b x)) := by
  have hc : Continuous (fun A : V [×0]→L[ℝ] W => A (fun i => Fin.elim0 i)) := by fun_prop
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    hc.continuousAt.tendsto.comp h

variable {σ : ℕ → ℕ} {b : L.limitCarrier.carrier → ℝ}
  (hjets : ∀ z : L.limitCarrier.carrier, ∀ m K,
    IsCompact K → K ⊆ (extChartAt (𝓡 3) z).target →
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (G.normalizedPotentialPullback L (σ k) ∘ (extChartAt (𝓡 3) z).symm))
      (iteratedFDeriv ℝ m (b ∘ (extChartAt (𝓡 3) z).symm)) atTop K)

include hjets

theorem normalizedPotential_limit_base : b L.base = 0 := by
  have h := (hjets L.base 0 {(extChartAt (𝓡 3) L.base) L.base}
    isCompact_singleton (singleton_subset_iff.mpr (mem_extChartAt_target L.base))).tendsto_at
      (mem_singleton _)
  have hc : Continuous (fun A : E [×0]→L[ℝ] ℝ => A (fun i => Fin.elim0 i)) := by fun_prop
  have hh := hc.continuousAt.tendsto.comp h
  simp only [Function.comp_def, iteratedFDeriv_zero_apply, extChartAt_to_inv,
    G.normalizedPotentialPullback_base] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds



theorem normalizedPotential_limit_coordinate_hessian
    (hσ : StrictMono σ) (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (z : L.limitCarrier.carrier) (x : E) (hx : x ∈ (extChartAt (𝓡 3) z).target)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (b ∘ (extChartAt (𝓡 3) z).symm)) x v w =
      fderiv ℝ (b ∘ (extChartAt (𝓡 3) z).symm) x
        (CoordinateExponential.christoffelBilinear
          ((L.limitFlow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) z).symm) x v w) := by
  let c := (extChartAt (𝓡 3) z).symm
  let f := fun k => G.normalizedPotentialPullback L (σ k) ∘ c
  let B := fun k y => G.normalizedPotentialSpacetimeCoefficients L z (σ k) (0, y)
  let B₀ := (L.limitFlow.metric 0).pullbackCoefficients c
  have hJ (m : ℕ) := (hjets z m {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
    (mem_singleton x)
  have hd : Tendsto (fun k => fderiv ℝ (f k) x) atTop (𝓝 (fderiv ℝ (b ∘ c) x)) :=
    tendsto_fderiv_of_jet_one (hJ 1)
  have heval : Continuous (fun A : E [×2]→L[ℝ] ℝ => A ![v, w]) := by fun_prop
  have hdd := heval.continuousAt.tendsto.comp (hJ 2)
  simp only [Function.comp_def, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hdd
  have hBJ (m : ℕ) := ((G.normalizedPotentialCoefficients_smooth_convergence L z).2
    m {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
  have hB : Tendsto (fun k => B k x) atTop (𝓝 (B₀ x)) :=
    (tendsto_value_of_jet_zero (hBJ 0)).comp hσ.tendsto_atTop
  have hdB : Tendsto (fun k => fderiv ℝ (B k) x) atTop (𝓝 (fderiv ℝ B₀ x)) :=
    (tendsto_fderiv_of_jet_one (hBJ 1)).comp hσ.tendsto_atTop
  have hi := ((L.limitFlow.metric 0).isInvertible_chartCoefficients z hx).contDiffAt_map_inverse
    (n := ∞) |>.continuousAt.tendsto.comp hB
  have hkoszul : Continuous (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ =>
      metricKoszulCovector A v w) := by
    have hflip : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    have hflip' : Continuous (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous
    unfold metricKoszulCovector
    fun_prop
  have hΓ := tendsto_clm_apply hi (hkoszul.continuousAt.tendsto.comp hdB)
  change Tendsto (fun k => CoordinateExponential.christoffelBilinear (B k) x v w) atTop
    (𝓝 (CoordinateExponential.christoffelBilinear B₀ x v w)) at hΓ
  have hmain := tendsto_clm_apply hd hΓ
  let H₀ := fun a : ℝ × E => (L.limitFlow.metric a.1).pullbackCoefficients c a.2
  have hH := (G.normalizedPotentialSpacetimeCoefficients_tendsto_jets L z 1
    (K := {(0, x)}) isCompact_singleton
    (singleton_subset_iff.mpr ⟨by norm_num, hx⟩)).tendsto_at (mem_singleton (0, x))
  have htime := tendsto_clm_apply
    ((tendsto_fderiv_of_jet_one hH).comp hσ.tendsto_atTop)
    (tendsto_const_nhds (x := (1, (0 : E))))
  have hnum := (tendsto_clm_apply (tendsto_clm_apply (hB.add htime)
    (tendsto_const_nhds (x := v))) (tendsto_const_nhds (x := w)))
  have hscale := (G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape).comp
    hσ.tendsto_atTop
  have hforce := hnum.div_atTop (hscale.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hdom := (G.normalizedPotential_chart_eventually_domain L z {x} isCompact_singleton
    (singleton_subset_iff.mpr hx)).filter_mono hσ.tendsto_atTop
  have hsum := hmain.add hforce
  simp only [add_zero] at hsum
  apply tendsto_nhds_unique hdd
  apply hsum.congr'
  filter_upwards [hdom] with k hk
  have hh := G.normalizedPotentialPullback_fderiv2 L z (σ k) x hx (hk x (mem_singleton x)) v w
  dsimp only at hh
  rw [G.normalizedPotentialSpacetimeCoefficients_deriv_time L z (σ k) x hx
    (hk x (mem_singleton x))] at hh
  exact hh.symm


theorem normalizedPotential_limit_hasZeroHessian
    (hσ : StrictMono σ) (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b) :
    RiemannianMetric.HasZeroHessian (L.limitFlow.connection 0) b := by
  intro z v w
  let c := extChartAt (𝓡 3) z
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm z
  have hi (y : E) (hy : y ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hy)
  let A : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) c.symm (c z)
  have hA : A.IsInvertible := hi (c z) (mem_extChartAt_target z)
  have hh := (L.limitFlow.connection 0).hessian_in_smooth_parametrization
    (isOpen_extChartAt_target z) hc hi (mem_extChartAt_target z)
    (hb (c.symm (c z))) (A.inverse v) (A.inverse w)
  rw [G.normalizedPotential_limit_coordinate_hessian L hjets hσ hD p hescape z (c z)
    (mem_extChartAt_target z) (A.inverse v) (A.inverse w), sub_self] at hh
  have hcz : c.symm (c z) = z := c.left_inv (mem_extChartAt_source z)
  change (L.limitFlow.connection 0).hessian b (c.symm (c z))
    (A (A.inverse v)) (A (A.inverse w)) = 0 at hh
  have hv : A (A.inverse v) = v := hA.self_apply_inverse v
  have hw : A (A.inverse w) = w := hA.self_apply_inverse w
  rw [hcz, hv, hw] at hh
  exact hh

omit hjets in
private theorem normalizedPotential_source_chart_energy (z : L.limitCarrier.carrier)
    (k : ℕ) (x : E) (hx : x ∈ (extChartAt (𝓡 3) z).target)
    (hxk : (extChartAt (𝓡 3) z).symm x ∈ L.exhaustion k) :
    let f := G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm
    let B := G.normalizedPotentialSpacetimeCoefficients L z k (0, x)
    S.metric.inner (G.unscaledOriginalEmbedding L k ((extChartAt (𝓡 3) z).symm x))
      (S.connection.gradient (S.normalizedPotential (q (L.subsequence k)))
        (G.unscaledOriginalEmbedding L k ((extChartAt (𝓡 3) z).symm x)))
      (S.connection.gradient (S.normalizedPotential (q (L.subsequence k)))
        (G.unscaledOriginalEmbedding L k ((extChartAt (𝓡 3) z).symm x))) =
      fderiv ℝ f x (B.inverse (fderiv ℝ f x)) := by
  let c := (extChartAt (𝓡 3) z).symm
  let e := G.unscaledOriginalEmbedding L k ∘ c
  let eS := L.embedding k ∘ c
  let d := (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c x :=
    (contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds hx)
  have hiE : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (G.unscaledOriginalEmbedding L k) (c x) :=
    (L.embedding_smooth k ⟨c x, hxk⟩).comp (𝓡 3) M (d.isLocalDiffeomorph _)
  have hiC : (mfderiv (𝓡 3) (𝓡 3) c x).IsInvertible := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hx)
  have he := hiE.contMDiffAt.comp x hc
  have hi : (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := by
    dsimp only [e]
    rw [mfderiv_comp x (hiE.contMDiffAt.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))]
    exact (show (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) (c x)).IsInvertible
      from ⟨hiE.mfderivToContinuousLinearEquiv (by simp), rfl⟩).comp hiC
  have hmetric : S.metric.pullbackCoefficients e x =
      G.normalizedPotentialSpacetimeCoefficients L z k (0, x) := by
    ext v w
    have hsmall : MDifferentiableAt (𝓡 3) (𝓡 3) eS x :=
      (((L.embedding_smooth k ⟨c x, hxk⟩).contMDiffAt.comp x hc).mdifferentiableAt (by simp))
    change S.metric.inner (d (eS x))
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ eS) x v)
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ eS) x w) = _
    rw [mfderiv_comp x (d.contMDiff.mdifferentiable (by simp) _) hsmall]
    change S.metric.inner _ _ _ = (G.unscaledSourceFlow.metric 0).inner _ _ _
    rw [G.unscaledSourceFlow_metric_zero]
    rfl
  have hh := S.connection.gradient_normSq_in_parametrization
    (he.mdifferentiableAt (by simp)) hi
    ((S.normalizedPotential_contMDiff (q (L.subsequence k)) (e x)).mdifferentiableAt (by simp))
  rw [hmetric] at hh
  exact hh


theorem normalizedPotential_limit_unit_at_base
    (hσ : StrictMono σ) (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b) :
    (L.limitFlow.metric 0).inner L.base
      ((L.limitFlow.connection 0).gradient b L.base)
      ((L.limitFlow.connection 0).gradient b L.base) = 1 := by
  let c := extChartAt (𝓡 3) L.base
  let x := c L.base
  let B := fun k => G.normalizedPotentialSpacetimeCoefficients L L.base (σ k) (0, x)
  let B₀ := (L.limitFlow.metric 0).pullbackCoefficients c.symm x
  let f := fun k => G.normalizedPotentialPullback L (σ k) ∘ c.symm
  have hx : x ∈ c.target := mem_extChartAt_target L.base
  have hcx : c.symm x = L.base := c.left_inv (mem_extChartAt_source L.base)
  have hB := (tendsto_value_of_jet_zero
    (((G.normalizedPotentialCoefficients_smooth_convergence L L.base).2 0 {x}
      isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x))).comp
      hσ.tendsto_atTop
  have hd : Tendsto (fun k => fderiv ℝ (f k) x) atTop (𝓝 (fderiv ℝ (b ∘ c.symm) x)) :=
    tendsto_fderiv_of_jet_one ((hjets L.base 1 {x} isCompact_singleton
      (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x))
  have hi := ((L.limitFlow.metric 0).isInvertible_chartCoefficients L.base hx).contDiffAt_map_inverse
    (n := ∞) |>.continuousAt.tendsto.comp hB
  have henergy := tendsto_clm_apply hd (tendsto_clm_apply hi hd)
  have hdom := (G.normalizedPotential_chart_eventually_domain L L.base {x}
    isCompact_singleton (singleton_subset_iff.mpr hx)).filter_mono hσ.tendsto_atTop
  have hscale := (G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape).comp
    hσ.tendsto_atTop
  have hone : ∀ᶠ k in atTop, fderiv ℝ (f k) x ((B k).inverse (fderiv ℝ (f k) x)) = 1 := by
    filter_upwards [hdom, hscale.eventually_gt_atTop 0] with k hk hpos
    have hh := G.normalizedPotential_source_chart_energy L L.base (σ k) x hx
      (hk x (mem_singleton x))
    dsimp only at hh
    change S.metric.inner (G.unscaledOriginalEmbedding L (σ k) (c.symm x))
      (S.connection.gradient (S.normalizedPotential (q (L.subsequence (σ k))))
        (G.unscaledOriginalEmbedding L (σ k) (c.symm x)))
      (S.connection.gradient (S.normalizedPotential (q (L.subsequence (σ k))))
        (G.unscaledOriginalEmbedding L (σ k) (c.symm x))) = _ at hh
    rw [hcx, G.unscaledOriginalEmbedding_base] at hh
    rw [S.normalizedPotential_gradient_sq_center hpos] at hh
    exact hh.symm
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm (n := ∞) L.base).contMDiffAt
      ((isOpen_extChartAt_target L.base).mem_nhds hx)
  have hiC : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
    simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hx)
  have hlimit := (L.limitFlow.connection 0).gradient_normSq_in_parametrization
    (hc.mdifferentiableAt (by simp)) hiC ((hb (c.symm x)).mdifferentiableAt (by simp))
  rw [hcx] at hlimit
  rw [hlimit]
  exact tendsto_nhds_unique henergy (tendsto_const_nhds.congr' (hone.mono fun _ h => h.symm))



theorem normalizedPotential_limit_hasUnitGradient
    (hσ : StrictMono σ) (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b) :
    RiemannianMetric.HasUnitGradient (L.limitFlow.connection 0) b := by
  let : PreconnectedSpace L.limitCarrier.carrier := ⟨L.limitCarrier.connected.isPreconnected⟩
  have hz := G.normalizedPotential_limit_hasZeroHessian L hjets hσ hD p hescape hb
  let D := L.limitFlow.connection 0
  let g := L.limitFlow.metric 0
  have he : MDifferentiable (𝓡 3) 𝓘(ℝ, ℝ)
      (fun x => g.inner x (D.gradient b x) (D.gradient b x)) := by
    intro x
    have hgrad := D.contMDiffAt_gradient (hb x)
    have h := ((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad
    exact ((Bundle.contMDiffAt_totalSpace.mp h).2).mdifferentiableAt (by simp)
  intro x
  calc
    g.inner x (D.gradient b x) (D.gradient b x) =
        g.inner L.base (D.gradient b L.base) (D.gradient b L.base) := by
      apply Poincare.Manifold.eq_of_mvfderiv_eq_zero he
      intro y v
      rw [D.mvfderiv_gradient_normSq (hb y), hz y v, mul_zero]
    _ = 1 := G.normalizedPotential_limit_unit_at_base L hjets hσ hD p hescape hb



theorem normalizedPotential_limit_identities
    (hσ : StrictMono σ) (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hb : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b) :
    b L.base = 0 ∧ RiemannianMetric.HasUnitGradient (L.limitFlow.connection 0) b ∧
      RiemannianMetric.HasZeroHessian (L.limitFlow.connection 0) b :=
  ⟨G.normalizedPotential_limit_base L hjets,
    G.normalizedPotential_limit_hasUnitGradient L hjets hσ hD p hescape hb,
    G.normalizedPotential_limit_hasZeroHessian L hjets hσ hD p hescape hb⟩

end PoincareConjecture.ShrinkingSolitonFlow
