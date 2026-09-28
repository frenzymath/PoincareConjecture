import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateTest

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientAsymptoticSolitonPredecessors

variable {K : AncientKappaSolution n M}

theorem reducedLength_locallyLipschitzOn_smooth_coordinates
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source) :
    LocallyLipschitzOn e.source (fun x ↦ reducedLength K.flow 0 p (e x) τ) := by
  intro x hx
  obtain ⟨U, hU, haU, hUt, C, hCL⟩ := P.reducedLength_lipschitz_coordinate_neighborhoods p hτ (e x)
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (e x)
  have heAt := he.contMDiffAt (e.open_source.mem_nhds hx)
  have hcAt : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (e x) :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds (mem_chart_source _ _))
  have hce : ContDiffAt ℝ ∞ (c ∘ e) x := (hcAt.comp x heAt).contDiffAt
  obtain ⟨L, W, hW, hWL⟩ := (hce.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).exists_lipschitzOnWith
  let T := W ∩ (c ∘ e) ⁻¹' U ∩ e ⁻¹' c.source
  have hT : T ∈ 𝓝 x := inter_mem
    (inter_mem hW (hce.continuousAt.preimage_mem_nhds (hU.mem_nhds haU)))
    (heAt.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds (mem_chart_source _ _)))
  refine ⟨C * L, T, mem_nhdsWithin_of_mem_nhds hT, ?_⟩
  intro y hy z hz
  have h := (hCL.comp (hWL.mono (fun _ hw ↦ hw.1.1)) (fun _ hw ↦ hw.1.2)) hy hz
  change edist (reducedLength K.flow 0 p (c.symm (c (e y))) τ)
    (reducedLength K.flow 0 p (c.symm (c (e z))) τ) ≤ _ at h
  simpa only [Function.comp_apply, c.left_inv hy.2, c.left_inv hz.2] using h

theorem reducedLength_lipschitzOn_compact_coordinates
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) (hAs : A ⊆ e.source) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun x ↦ reducedLength K.flow 0 p (e x) τ) A :=
  ((P.reducedLength_locallyLipschitzOn_smooth_coordinates p hτ e he).mono hAs).exists_lipschitzOnWith_of_compact hA

end AncientAsymptoticSolitonPredecessors

namespace LeviCivitaData

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
theorem coordinateGradient_eq_inverse_fderiv
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x =
      (g.pullbackCoefficients e x).inverse (fderiv ℝ (φ ∘ e) x) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hi : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  symm
  apply (g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)).inverse_apply_eq.mpr
  ext v
  have hh := congrArg (fun A ↦ A v) (mvfderiv_comp x
    ((hφ (e x)).mdifferentiableAt (by simp)) (hD.mdifferentiableAt hx))
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at hh
  change fderiv ℝ (φ ∘ e) x v = g.inner (e x)
    (mfderiv (𝓡 n) (𝓡 n) e x (mpullback (𝓡 n) (𝓡 n) e (D.gradient φ) x))
      (mfderiv (𝓡 n) (𝓡 n) e x v)
  simp only [mpullback, hi.self_apply_inverse, D.inner_gradient]
  convert! hh using 1

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
theorem pullback_inverse_pairing_comm
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (he : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e x))
    (a b : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    a ((g.pullbackCoefficients e x).inverse b) =
      b ((g.pullbackCoefficients e x).inverse a) := by
  have hi := g.isInvertible_pullbackCoefficients he
  have h := g.symm (e x)
    (mfderiv (𝓡 n) (𝓡 n) e x ((g.pullbackCoefficients e x).inverse a))
    (mfderiv (𝓡 n) (𝓡 n) e x ((g.pullbackCoefficients e x).inverse b))
  change g.pullbackCoefficients e x ((g.pullbackCoefficients e x).inverse a)
    ((g.pullbackCoefficients e x).inverse b) =
    g.pullbackCoefficients e x ((g.pullbackCoefficients e x).inverse b)
      ((g.pullbackCoefficients e x).inverse a) at h
  simpa only [hi.self_apply_inverse] using h

end LeviCivitaData

namespace AncientAsymptoticSolitonPredecessors

open LeviCivitaData.Dirichlet

private theorem linearMap_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

theorem reducedLength_weak_coordinate_gradient_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := K.flow.metric (0 - τ)
    let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
    IntegrableOn (fun x ↦ g.pullbackVolumeDensity e x *
      fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) O ∧
    -(∫ x in O, g.pullbackVolumeDensity e x *
      fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) ≤
      ∫ x in O, ((l x + (n : ℝ) / 2) / τ) * g.pullbackVolumeDensity e x * φ x := by
  classical
  let g := K.flow.metric (0 - τ)
  let D := K.flow.connection (0 - τ)
  let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
  let ψ := coordinateExtension e φ
  have hOsource : O ⊆ e.source := subset_closure.trans hOs
  have hφs : tsupport φ ⊆ e.source := hφO.trans hOsource
  have hψ := contMDiff_coordinateExtension e hei hφ hφc hφs
  have hψc := hasCompactSupport_coordinateExtension e hφc hφs
  have hψs : tsupport ψ ⊆ e.target := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_coordinateExtension_subset_image e hφc hφs hy
    exact e.map_source (hφs hx)
  have hψφ {x} (hx : x ∈ e.source) : (ψ ∘ e) =ᶠ[𝓝 x] φ := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact coordinateExtension_comp_apply e φ hy
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x ↦
    g.pullbackVolumeDensity e x * WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient ψ) x) i
  let W : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i ↦ e.source.indicator (V i)
  have hWgerm (i) (x) (hx : x ∈ e.source) : W i =ᶠ[𝓝 x] V i := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  have hWs (i : Fin n) : tsupport (W i) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_cases hxs : x ∈ e.source
    · by_contra hxφ
      have hxψ : e x ∉ tsupport ψ := by
        intro h
        obtain ⟨y, hy, hyx⟩ := tsupport_coordinateExtension_subset_image e hφc hφs h
        exact hxφ ((e.injOn (hφs hy) hxs hyx) ▸ hy)
      exact hx (by simp [W, indicator_of_mem hxs, V, mpullback,
        D.gradient_eq_zero_of_notMem_tsupport hxψ])
    · exact False.elim (hx (indicator_of_notMem hxs _))
  have hW (i : Fin n) : ContDiff ℝ ∞ (W i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.source
    · exact (D.contDiffAt_coordinateGradientFlux e he hei hx (hψ (e x)) i).congr_of_eventuallyEq
        (hWgerm i x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun ht ↦ hx (hφs (hWs i ht))))
  have hWc (i : Fin n) : HasCompactSupport (W i) :=
    hφc.isCompact.of_isClosed_subset (isClosed_tsupport _) (hWs i)
  obtain ⟨C, hLip⟩ := P.reducedLength_lipschitzOn_compact_coordinates p hτ e he hOc hOs
  have hp := Poincare.Analysis.WeakDerivative.integral_mul_sum_fderiv_eq_neg
    volume hO (hLip.mono subset_closure) (EuclideanSpace.basisFun (Fin n) ℝ) W hW hWc
    (fun i ↦ (hWs i).trans hφO)
  let H := fun x ↦ ∑ i, fderiv ℝ l x (EuclideanSpace.basisFun (Fin n) ℝ i) * W i x
  let Q := fun x ↦ g.pullbackVolumeDensity e x *
    fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hHQ : H = O.indicator Q := by
    funext x
    by_cases hx : x ∈ O
    · rw [indicator_of_mem hx]
      calc
        H x = fderiv ℝ l x (mpullback (𝓡 n) (𝓡 n) e (D.gradient ψ) x) *
            g.pullbackVolumeDensity e x := by
          rw [linearMap_eq_sum_coordinates, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          simp only [W, indicator_of_mem (hOsource hx), V]
          ring
        _ = Q x := by
          rw [D.coordinateGradient_eq_inverse_fderiv e he hei hψ (hOsource hx),
            (hψφ (hOsource hx)).fderiv_eq,
            LeviCivitaData.pullback_inverse_pairing_comm g (hD.mfderiv_injective (hOsource hx))]
          ring
    · rw [indicator_of_notMem hx]
      apply Finset.sum_eq_zero
      intro i _
      rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hφO (hWs i ht))), mul_zero]
  have hleft : (∫ x, l x * ∑ i, fderiv ℝ (W i) x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      ∫ q, reducedLength K.flow 0 p q τ * D.laplacian ψ q ∂g.volumeMeasure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.source) (fun x hx ↦ ?_)]
    · calc
        _ = ∫ x in e.source, (l x * D.laplacian ψ (e x)) * g.pullbackVolumeDensity e x := by
          apply setIntegral_congr_fun e.open_source.measurableSet
          intro x hx
          have heq (i : Fin n) : fderiv ℝ (W i) x = fderiv ℝ (V i) x :=
            (hWgerm i x hx).fderiv_eq
          simp_rw [heq]
          rw [← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hψ (e x))]
          ring
        _ = ∫ q in e.target, reducedLength K.flow 0 p q τ * D.laplacian ψ q ∂g.volumeMeasure :=
          (g.integral_target_eq_integral_pullback_density e he hei
            ((P.continuous_reducedLength p τ hτ).mul (D.continuous_laplacian hψ)).continuousOn).symm
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun q hq ↦ by
          rw [D.laplacian_eq_zero_of_notMem_tsupport (fun ht ↦ hq (hψs ht)), mul_zero])
    · have hz (i) : fderiv ℝ (W i) x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht ↦ hx (hφs (hWs i (tsupport_fderiv_subset ℝ ht))))
      simp [hz]
  have hright : (∫ q, ψ q * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ) ∂g.volumeMeasure) =
      ∫ x in O, ((l x + (n : ℝ) / 2) / τ) * g.pullbackVolumeDensity e x * φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target)
      (fun q hq ↦ by rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hq (hψs ht)), zero_mul])]
    have hcont : Continuous (fun q ↦ ψ q * ((reducedLength K.flow 0 p q τ + (n : ℝ) / 2) / τ)) :=
      hψ.continuous.mul (((P.continuous_reducedLength p τ hτ).add continuous_const).div_const τ)
    rw [g.integral_target_eq_integral_pullback_density e he hei hcont.continuousOn]
    calc
      _ = ∫ x in e.source, ((l x + (n : ℝ) / 2) / τ) * g.pullbackVolumeDensity e x * φ x := by
        apply setIntegral_congr_fun e.open_source.measurableSet
        intro x hx
        dsimp only [ψ]
        rw [coordinateExtension_comp_apply e φ hx]
        ring
      _ = _ := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_source.measurableSet hOsource
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hφO ht)), mul_zero]
  have hw := P.reducedLength_weak_laplacian_le p hτ hψ hψc (fun q ↦ by
    dsimp [ψ, coordinateExtension]
    by_cases hq : q ∈ e.target
    · simpa [indicator_of_mem hq] using hφ0 (e.symm q)
    · simp [indicator_of_notMem hq])
  simp_rw [calibratedMetricVolume_eq_volumeMeasure] at hw
  rw [← hleft, hp.2.2, hright] at hw
  change -(∫ x, H x) ≤ _ at hw
  rw [hHQ, integral_indicator hO.measurableSet] at hw
  have hHi : Integrable H := hp.1
  rw [hHQ] at hHi
  exact ⟨(integrable_indicator_iff hO.measurableSet).mp hHi, hw⟩

theorem reducedLength_weak_coordinate_divergence_le
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOs : closure O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := K.flow.metric (0 - τ)
    let l := fun x ↦ reducedLength K.flow 0 p (e x) τ
    (∫ x in O, ∑ i : Fin n,
      (-g.pullbackVolumeDensity e x *
        WithLp.ofLp ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) i) *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) ≤
      ∫ x in O, ((l x + (n : ℝ) / 2) / τ) * g.pullbackVolumeDensity e x * φ x := by
  have h := (P.reducedLength_weak_coordinate_gradient_le p hτ e he hei hO hOc hOs
    hφ hφc hφO hφ0).2
  dsimp only at h ⊢
  rw [← integral_neg] at h
  convert h using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    conv_rhs => rw [linearMap_eq_sum_coordinates]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [EuclideanSpace.basisFun_apply]
    ring

end AncientAsymptoticSolitonPredecessors
end PoincareConjecture
