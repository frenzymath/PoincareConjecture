import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.RegularMeasure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem reducedLengthGradientNormSq_eq_gradient_norm_sq {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (f : M × ℝ → ℝ) (τ : ℝ) (q : M) :
    reducedLengthGradientNormSq F T f τ q =
      ((F.metric (T - τ)).tangentNorm q
        ((F.connection (T - τ)).gradient (fun x => f (x, τ)) q)) ^ 2 := by
  let g := F.metric (T - τ)
  let D := F.connection (T - τ)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis q
  have h := b.sum_sq_norm_inner_left (D.gradient (fun x => f (x, τ)) q)
  have hn : ‖D.gradient (fun x => f (x, τ)) q‖ =
      g.tangentNorm q (D.gradient (fun x => f (x, τ)) q) := rfl
  rw [hn] at h
  change (∑ i, (mvfderiv (𝓡 n) (fun x => f (x, τ)) q (b i)) ^ 2) = _
  simp only [Real.norm_eq_abs, sq_abs] at h
  simpa only [show ∀ v, inner ℝ (D.gradient (fun x => f (x, τ)) q) v =
      mvfderiv (𝓡 n) (fun x => f (x, τ)) q v from D.inner_gradient _ q]
    using h

variable [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace RiemannianMetric

omit [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] in


theorem ae_mem_open_in_coordinates (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {G : Set M} (hG : IsOpen G) (hnull : g.volumeMeasure Gᶜ = 0) :
    ∀ᵐ x ∂volume, x ∈ e.source → e x ∈ G := by
  let s := e.source \ (e.source ∩ e ⁻¹' G)
  have hs : MeasurableSet s := e.open_source.measurableSet.diff
    (e.continuousOn.isOpen_inter_preimage e.open_source hG).measurableSet
  have hse : s ⊆ e.source := sdiff_subset
  have himage : g.volumeMeasure (e '' s) = 0 := by
    apply measure_mono_null _ hnull
    rintro _ ⟨x, hx, rfl⟩
    exact fun hxG => hx.2 ⟨hx.1, hxG⟩
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ s) :=
    g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx.1)) (hD.mfderiv_injective hx.1)
  have hρc : ContinuousOn (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x)) s :=
    fun x hx => (ENNReal.continuous_ofReal.continuousAt.comp
      (hρ x hx).1.continuousAt).continuousWithinAt
  have hz : ∀ᵐ x ∂volume.restrict s, ENNReal.ofReal (g.pullbackVolumeDensity e x) = 0 := by
    apply (lintegral_eq_zero_iff' (hρc.aemeasurable hs)).mp
    rw [← g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei hs hse]
    exact himage
  have hfalse : ∀ᵐ x ∂volume.restrict s, False := by
    filter_upwards [hz, ae_restrict_mem hs] with x hx hxs
    exact (ENNReal.ofReal_pos.mpr (hρ x hxs).2).ne' hx
  have hsnull : volume s = 0 := by simpa using hfalse
  apply ae_iff.mpr
  convert hsnull using 1
  congr 1
  ext x
  simp [s]

end RiemannianMetric

namespace AncientAsymptoticSolitonPredecessors


theorem regular_reducedLength_spatial_eventuallyEq {K : AncientKappaSolution n M}
    {R τ : ℝ} {p q : M} (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    (fun x => reducedLength K.flow 0 p x τ) =ᶠ[𝓝 q]
      (fun x => r.representative (x, τ)) := by
  have hn := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
    (r.neighborhood_open.mem_nhds r.center_mem)
  filter_upwards [hn] with x hx
  exact (r.representative_eq (x, τ) hx).symm


theorem regular_reducedLength_spatial_smooth {K : AncientKappaSolution n M}
    {R τ : ℝ} {p q : M} (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => reducedLength K.flow 0 p x τ) q :=
  r.representative_space_smooth.congr_of_eventuallyEq
    (regular_reducedLength_spatial_eventuallyEq r)


theorem regular_reducedLength_differential_bound {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) (v : TangentSpace (𝓡 n) q) :
    |mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) q v| ≤
      Real.sqrt (3 * reducedLength K.flow 0 p q τ / τ) *
        (K.flow.metric (0 - τ)).tangentNorm q v := by
  have h := P.regular_reducedLength_gradient_bound r
  have hR := ((Classical.choice P.structural).structural M K).scalar_pos (0 - τ)
    (by linarith [r.tau_pos]) q
  have hgrad : ((K.flow.metric (0 - τ)).tangentNorm q
      ((K.flow.connection (0 - τ)).gradient (fun x => r.representative (x, τ)) q)) ^ 2 ≤
      3 * reducedLength K.flow 0 p q τ / τ := by
    rw [← reducedLengthGradientNormSq_eq_gradient_norm_sq]
    linarith
  have hnorm := (Real.sqrt_le_sqrt hgrad)
  rw [Real.sqrt_sq (show 0 ≤ (K.flow.metric (0 - τ)).tangentNorm q
    ((K.flow.connection (0 - τ)).gradient (fun x => r.representative (x, τ)) q)
      from Real.sqrt_nonneg _)] at hnorm
  have hd := (K.flow.connection (0 - τ)).abs_mvfderiv_le_gradient_norm
    (fun x => r.representative (x, τ)) q v
  have heq := regular_reducedLength_spatial_eventuallyEq r
  unfold mvfderiv
  rw [heq.mfderiv_eq]
  exact hd.trans (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _))



theorem regular_sqrt_reducedLength_differential_bound {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) (v : TangentSpace (𝓡 n) q) :
    |mvfderiv (𝓡 n) (fun x => Real.sqrt (reducedLength K.flow 0 p x τ)) q v| ≤
      (Real.sqrt (3 / τ) / 2) * (K.flow.metric (0 - τ)).tangentNorm q v := by
  let l := reducedLength K.flow 0 p q τ
  have hτ := r.tau_pos
  have hl : 0 < l := P.reducedLength_pos p q τ r.tau_pos
  have hs := regular_reducedLength_spatial_smooth r
  have hsqrt := Real.hasDerivAt_sqrt hl.ne'
  have hchain : mvfderiv (𝓡 n)
      (fun x => Real.sqrt (reducedLength K.flow 0 p x τ)) q v =
      (1 / (2 * Real.sqrt l)) *
        mvfderiv (𝓡 n) (fun x => reducedLength K.flow 0 p x τ) q v := by
    rw [show (fun x => Real.sqrt (reducedLength K.flow 0 p x τ)) =
        Real.sqrt ∘ (fun x => reducedLength K.flow 0 p x τ) from rfl,
      mvfderiv_comp q hsqrt.differentiableAt.mdifferentiableAt
        (hs.mdifferentiableAt (by simp))]
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    change (fderiv ℝ Real.sqrt l) _ = _
    rw [hsqrt.hasFDerivAt.fderiv]
    change (_ : ℝ) * _ = _ * _
    simp only [LinearMap.id_apply, NormedSpace.fromTangentSpace]
    exact mul_comm _ _
  rw [hchain, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt l))]
  have h := mul_le_mul_of_nonneg_left (P.regular_reducedLength_differential_bound r v)
    (by positivity : 0 ≤ 1 / (2 * Real.sqrt l))
  have heq : 1 / (2 * Real.sqrt l) * Real.sqrt (3 * l / τ) = Real.sqrt (3 / τ) / 2 := by
    rw [show 3 * l / τ = (3 / τ) * l by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 3 / τ)]
    field_simp
  calc
    _ ≤ 1 / (2 * Real.sqrt l) *
        (Real.sqrt (3 * l / τ) * (K.flow.metric (0 - τ)).tangentNorm q v) := h
    _ = _ := by rw [← mul_assoc, heq]



theorem sqrt_reducedLength_coordinates_locallyLipschitz
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    {R τ : ℝ} {p : M} (D : ReducedLengthMeasureData K.flow 0 R p)
    (hτ : 0 < τ) (hτR : τ < R)
    {e : EuclideanSpace ℝ (Fin n) → M} {V : Set (EuclideanSpace ℝ (Fin n))}
    (he : ∀ x ∈ V, ContinuousAt e x) {B : ℝ≥0}
    (hLip : ∀ x ∈ V, ∀ y ∈ V,
      (K.flow.metric (0 - τ)).edist (e x) (e y) ≤ (B : ℝ≥0∞) * EDist.edist x y) :
    LocallyLipschitzOn V (fun x => Real.sqrt (reducedLength K.flow 0 p (e x) τ)) := by
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have heLip : LipschitzOnWith B e V := by
    intro x hx y hy
    exact (((Classical.choice P.structural).structural M K).edist_monotone
      (0 - τ) 0 (by linarith) le_rfl (e x) (e y)).trans (hLip x hx y hy)
  have hpairLip : LipschitzOnWith B (fun x => (e x, τ)) V := by
    simpa using heLip.prodMk (LipschitzWith.const τ).lipschitzOnWith
  have hlocD : LocallyLipschitzOn (univ ×ˢ Ioo 0 R)
      (fun z : M × ℝ => reducedLength K.flow 0 p z.1 z.2) := D.locally_lipschitz
  intro x hx
  obtain ⟨L, W, hW, hWL⟩ := hlocD (x := (e x, τ)) ⟨mem_univ _, hτ, hτR⟩
  have hW' : W ∈ 𝓝 (e x, τ) := by
    rwa [nhdsWithin_eq_nhds.mpr ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, hτ, hτR⟩)] at hW
  let f := fun y => reducedLength K.flow 0 p (e y) τ
  have hfc : ContinuousAt f x := (P.continuous_reducedLength p τ hτ).continuousAt.comp (he x hx)
  obtain ⟨A, S, hS, hSL⟩ := (Real.contDiffAt_sqrt
    (P.reducedLength_pos p (e x) τ hτ).ne' (n := 1)).exists_lipschitzOnWith
  let T := V ∩ (fun y => (e y, τ)) ⁻¹' W ∩ f ⁻¹' S
  refine ⟨A * (L * B), T, ?_, ?_⟩
  · exact inter_mem (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (((he x hx).prodMk continuousAt_const).preimage_mem_nhds hW')))
        (mem_nhdsWithin_of_mem_nhds (hfc.preimage_mem_nhds hS))
  · apply hSL.comp
      (hWL.comp (hpairLip.mono (fun _ ht => ht.1.1)) (fun _ ht => ht.1.2))
    exact fun _ ht => ht.2



theorem ae_regular_in_coordinates {K : AncientKappaSolution n M}
    {R τ : ℝ} {p : M} (D : ReducedLengthMeasureData K.flow 0 R p)
    (hτ : 0 < τ) (hτR : τ < R)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    ∀ᵐ x ∂volume, x ∈ e.source → (e x, τ) ∈ D.regularDomain := by
  apply (K.flow.metric (0 - τ)).ae_mem_open_in_coordinates e he hei
    (D.regularDomain_open.preimage (continuous_id.prodMk continuous_const))
  rw [← calibratedMetricVolume_eq_volumeMeasure]
  exact D.slice_complement_null τ hτ hτR



theorem regular_sqrt_reducedLength_coordinate_derivative
    {K : AncientKappaSolution n M} (P : AncientAsymptoticSolitonPredecessors K)
    {R τ : ℝ} {p : M} {e : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (r : ReducedLengthRegularPoint K.flow 0 R p (e x) τ)
    {B : ℝ≥0} (hB : ∀ v : EuclideanSpace ℝ (Fin n),
      (K.flow.metric (0 - τ)).tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ B * ‖v‖) :
    DifferentiableAt ℝ (fun z => Real.sqrt (reducedLength K.flow 0 p (e z) τ)) x ∧
      ‖fderiv ℝ (fun z => Real.sqrt (reducedLength K.flow 0 p (e z) τ)) x‖ ≤
        (Real.sqrt (3 / τ) / 2) * B := by
  let f := fun q => Real.sqrt (reducedLength K.flow 0 p q τ)
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x) :=
    (Real.contDiffAt_sqrt (P.reducedLength_pos p (e x) τ r.tau_pos).ne').comp_contMDiffAt
      (f := fun q => reducedLength K.flow 0 p q τ) (regular_reducedLength_spatial_smooth r)
  have hd := (hf.comp x he).mdifferentiableAt (by simp)
  refine ⟨hd.differentiableAt, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hchain : fderiv ℝ (fun z => f (e z)) x v =
      mvfderiv (𝓡 n) f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
    have h := mvfderiv_comp x (hf.mdifferentiableAt (by simp))
      (he.mdifferentiableAt (by simp))
    have hh := congrArg (fun A => A v) h
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      Function.comp_def] at hh
    exact hh
  rw [Real.norm_eq_abs, hchain]
  exact (P.regular_sqrt_reducedLength_differential_bound r _).trans
    ((mul_le_mul_of_nonneg_left (hB v) (by positivity)).trans_eq (by ring))

end AncientAsymptoticSolitonPredecessors

end PoincareConjecture
