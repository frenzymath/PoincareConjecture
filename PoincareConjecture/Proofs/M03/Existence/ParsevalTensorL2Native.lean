import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorDecodeNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u v

namespace PoincareConjecture.ParsevalTensorNative

open TensorProbeNative (Coefficients)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

abbrev ProjectionKernel (iota : Type v) := (iota × iota) → (iota × iota) → ℝ

def projectionKernel (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (ab cd : iota × iota) : ℝ :=
  g.inner x (F cd.1 x) (F ab.1 x) * g.inner x (F cd.2 x) (F ab.2 x)

theorem projectionKernel_continuous (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) :
    Continuous (projectionKernel g F) := by
  apply continuous_pi
  intro ab
  apply continuous_pi
  intro cd
  exact (TensorProbeNative.continuous_pairing (TensorProbeNative.metricTensor g)
    (F cd.1) (F ab.1)).mul
      (TensorProbeNative.continuous_pairing (TensorProbeNative.metricTensor g)
        (F cd.2) (F ab.2))

theorem nativeProjection_eq_kernel (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (C : Coefficients iota) (ab : iota × iota) :
    nativeProjection g F x C ab = ∑ cd : iota × iota, C cd * projectionKernel g F x ab cd := by
  rcases ab with ⟨a, b⟩
  simp only [nativeProjection_apply, nativeDecode_apply, projectionKernel, mul_assoc]

theorem nativeProjection_norm_le (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (x : M) (C : Coefficients iota) : ‖nativeProjection g F x C‖ ≤ ‖C‖ := by
  calc
    ‖nativeProjection g F x C‖ ≤ ‖nativeProjection g F x‖ * ‖C‖ :=
      (nativeProjection g F x).le_opNorm C
    _ ≤ 1 * ‖C‖ := mul_le_mul_of_nonneg_right
      (nativeProjection_opNorm_le_one g F hF x) (norm_nonneg C)
    _ = ‖C‖ := one_mul _

theorem nativeProjection_idempotent (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (x : M) (C : Coefficients iota) :
    nativeProjection g F x (nativeProjection g F x C) = nativeProjection g F x C := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact projection_idempotent (fun a => F a x) (hF x) C

theorem nativeProjection_selfadjoint (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (C D : Coefficients iota) :
    inner ℝ (nativeProjection g F x C) D = inner ℝ C (nativeProjection g F x D) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact projection_selfadjoint (fun a => F a x) C D

variable [MeasurableSpace M] [BorelSpace M]

theorem nativeProjection_aestronglyMeasurable (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (μ : Measure M) {f : M → Coefficients iota} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => nativeProjection g F x (f x)) μ := by
  have hcont : Continuous (fun p : ProjectionKernel iota × Coefficients iota =>
      WithLp.toLp 2 (fun ab : iota × iota => ∑ cd : iota × iota, p.2 cd * p.1 ab cd)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : iota × iota => ℝ)).comp
    apply continuous_pi
    intro ab
    apply continuous_finset_sum
    intro cd _
    exact ((EuclideanSpace.proj cd).continuous.comp continuous_snd).mul
      ((continuous_apply cd).comp ((continuous_apply ab).comp continuous_fst))
  have hm := hcont.comp_aestronglyMeasurable
    ((projectionKernel_continuous g F).aestronglyMeasurable.prodMk hf)
  convert hm using 1
  funext x
  apply PiLp.ext
  intro ab
  exact nativeProjection_eq_kernel g F x (f x) ab

theorem nativeProjection_memLp (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (μ : Measure M) {f : M → Coefficients iota} (hf : MemLp f 2 μ) :
    MemLp (fun x => nativeProjection g F x (f x)) 2 μ :=
  hf.of_le (nativeProjection_aestronglyMeasurable g F μ hf.aestronglyMeasurable)
    (Eventually.of_forall (fun x => nativeProjection_norm_le g F hF x (f x)))

variable (g : RiemannianMetric n M)
  (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
  (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
  (μ : Measure M)

def projectionL2Fun (f : Lp (Coefficients iota) 2 μ) : Lp (Coefficients iota) 2 μ :=
  (nativeProjection_memLp g F hF μ (Lp.memLp f)).toLp
    (fun x => nativeProjection g F x (f x))

theorem projectionL2Fun_coe (f : Lp (Coefficients iota) 2 μ) :
    projectionL2Fun g F hF μ f =ᵐ[μ] (fun x => nativeProjection g F x (f x)) :=
  (nativeProjection_memLp g F hF μ (Lp.memLp f)).coeFn_toLp

theorem norm_projectionL2Fun_le (f : Lp (Coefficients iota) 2 μ) :
    ‖projectionL2Fun g F hF μ f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [projectionL2Fun_coe g F hF μ f] with x hx
  rw [hx]
  exact nativeProjection_norm_le g F hF x (f x)

def projectionL2LinearMap : Lp (Coefficients iota) 2 μ →ₗ[ℝ] Lp (Coefficients iota) 2 μ where
  toFun := projectionL2Fun g F hF μ
  map_add' f k := by
    apply Lp.ext
    filter_upwards [projectionL2Fun_coe g F hF μ (f + k),
      projectionL2Fun_coe g F hF μ f, projectionL2Fun_coe g F hF μ k,
      Lp.coeFn_add f k, Lp.coeFn_add (projectionL2Fun g F hF μ f)
        (projectionL2Fun g F hF μ k)] with x hsum hf hk hi ho
    simp only [hsum, hi, ho, Pi.add_apply, hf, hk, map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [projectionL2Fun_coe g F hF μ (c • f),
      projectionL2Fun_coe g F hF μ f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (projectionL2Fun g F hF μ f)] with x hc hf hi ho
    simp only [RingHom.id_apply]
    simp only [hc, hi, ho, Pi.smul_apply, hf, map_smul]

def projectionL2 : Lp (Coefficients iota) 2 μ →L[ℝ] Lp (Coefficients iota) 2 μ :=
  (projectionL2LinearMap g F hF μ).mkContinuous 1 (fun f => by
    change ‖projectionL2Fun g F hF μ f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_projectionL2Fun_le g F hF μ f)

theorem projectionL2_coe (f : Lp (Coefficients iota) 2 μ) :
    projectionL2 g F hF μ f =ᵐ[μ] (fun x => nativeProjection g F x (f x)) :=
  projectionL2Fun_coe g F hF μ f

theorem norm_projectionL2_le (f : Lp (Coefficients iota) 2 μ) :
    ‖projectionL2 g F hF μ f‖ ≤ ‖f‖ := norm_projectionL2Fun_le g F hF μ f

theorem projectionL2_opNorm_le_one : ‖projectionL2 g F hF μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_projectionL2_le g F hF μ f

theorem projectionL2_idempotent (f : Lp (Coefficients iota) 2 μ) :
    projectionL2 g F hF μ (projectionL2 g F hF μ f) = projectionL2 g F hF μ f := by
  apply Lp.ext
  filter_upwards [projectionL2_coe g F hF μ (projectionL2 g F hF μ f),
    projectionL2_coe g F hF μ f] with x hpp hp
  rw [hpp, hp]
  exact nativeProjection_idempotent g F hF x (f x)

theorem projectionL2_selfadjoint (f k : Lp (Coefficients iota) 2 μ) :
    inner ℝ (projectionL2 g F hF μ f) k = inner ℝ f (projectionL2 g F hF μ k) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [projectionL2_coe g F hF μ f, projectionL2_coe g F hF μ k] with x hf hk
  rw [hf, hk]
  exact nativeProjection_selfadjoint g F x (f x) (k x)

variable [CompactSpace M] [IsFiniteMeasure μ]

theorem projectionL2_tensorToLp (h : TensorProbeNative.SmoothTensor (n := n) (M := M)) :
    projectionL2 g F hF μ (TensorProbeNative.tensorToLp F μ h) =
      TensorProbeNative.tensorToLp F μ h := by
  apply Lp.ext
  filter_upwards [projectionL2_coe g F hF μ (TensorProbeNative.tensorToLp F μ h),
    TensorProbeNative.tensorToLp_coe F μ h] with x hp ht
  rw [hp, ht]
  exact nativeProjection_probes g F hF h x

theorem projectionL2_eq_self_of_mem_tensorL2 {f : Lp (Coefficients iota) 2 μ}
    (hf : f ∈ TensorProbeNative.tensorL2 F μ) : projectionL2 g F hF μ f = f := by
  have hclosed : IsClosed {k : Lp (Coefficients iota) 2 μ | projectionL2 g F hF μ k = k} :=
    isClosed_eq (projectionL2 g F hF μ).continuous continuous_id
  have hclosure : closure (Set.range (TensorProbeNative.tensorToLp F μ)) ⊆
      {k : Lp (Coefficients iota) 2 μ | projectionL2 g F hF μ k = k} :=
    closure_minimal (by
      rintro _ ⟨h, rfl⟩
      exact projectionL2_tensorToLp g F hF μ h) hclosed
  exact hclosure hf

end PoincareConjecture.ParsevalTensorNative

end
