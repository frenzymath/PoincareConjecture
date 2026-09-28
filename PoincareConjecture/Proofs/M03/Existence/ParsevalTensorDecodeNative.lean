import PoincareConjecture.Proofs.M03.Existence.ParsevalMetricTraceNative

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

noncomputable section

universe u v

namespace PoincareConjecture.ParsevalTensorNative

open TensorProbeNative (Coefficients)

section LinearAlgebra

variable {V iota : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype iota]

def encode (F : iota → V) : (V →L[ℝ] V →L[ℝ] ℝ) →ₗ[ℝ] Coefficients iota where
  toFun h := WithLp.toLp 2 (fun ab : iota × iota => h (F ab.1) (F ab.2))
  map_add' h k := by ext ab; rfl
  map_smul' c h := by ext ab; rfl

@[simp] theorem encode_apply (F : iota → V) (h : V →L[ℝ] V →L[ℝ] ℝ)
    (a b : iota) : encode F h (a, b) = h (F a) (F b) := rfl

def decodeLinearMap (F : iota → V) : Coefficients iota →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) where
  toFun C := ∑ ab : iota × iota,
    C ab • (innerSL ℝ (F ab.1)).smulRight (innerSL ℝ (F ab.2))
  map_add' C D := by
    ext v w
    simp only [PiLp.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      smul_eq_mul, add_mul, Finset.sum_add_distrib]
  map_smul' c C := by
    simp only [PiLp.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul, RingHom.id_apply]

def decode (F : iota → V) (C : Coefficients iota) : V →L[ℝ] V →L[ℝ] ℝ :=
  decodeLinearMap F C

theorem decode_apply (F : iota → V) (C : Coefficients iota) (v w : V) :
    decode F C v w = ∑ ab : iota × iota,
      C ab * inner ℝ (F ab.1) v * inner ℝ (F ab.2) w := by
  change (∑ ab : iota × iota,
    C ab • (innerSL ℝ (F ab.1)).smulRight (innerSL ℝ (F ab.2))) v w = _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, mul_assoc]

theorem decode_encode (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (h : V →L[ℝ] V →L[ℝ] ℝ) : decode F (encode F h) = h := by
  ext v w
  rw [decode_apply, Fintype.sum_prod_type]
  have hleft : h v w = ∑ a, inner ℝ (F a) v * h (F a) w := by
    calc
      h v w = h (∑ a, inner ℝ (F a) v • F a) w := by rw [hF v]
      _ = _ := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro a _
  have hright : h (F a) w = ∑ b, inner ℝ (F b) w * h (F a) (F b) := by
    calc
      h (F a) w = h (F a) (∑ b, inner ℝ (F b) w • F b) := by rw [hF w]
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  rw [hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [encode_apply]
  ring

def projection (F : iota → V) : Coefficients iota →L[ℝ] Coefficients iota :=
  ((encode F).comp (decodeLinearMap F)).toContinuousLinearMap

theorem projection_apply (F : iota → V) (C : Coefficients iota) (ab : iota × iota) :
    projection F C ab = ∑ cd : iota × iota,
      C cd * inner ℝ (F cd.1) (F ab.1) * inner ℝ (F cd.2) (F ab.2) :=
  decode_apply F C (F ab.1) (F ab.2)

theorem projection_encode (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v)
    (h : V →L[ℝ] V →L[ℝ] ℝ) : projection F (encode F h) = encode F h := by
  change encode F (decode F (encode F h)) = encode F h
  rw [decode_encode F hF]

theorem projection_idempotent (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) (C : Coefficients iota) :
    projection F (projection F C) = projection F C :=
  projection_encode F hF (decode F C)

theorem coefficient_inner (C D : Coefficients iota) :
    inner ℝ C D = ∑ ab : iota × iota, C ab * D ab := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ab _
  change D ab * C ab = C ab * D ab
  exact mul_comm _ _

theorem projection_selfadjoint (F : iota → V) (C D : Coefficients iota) :
    inner ℝ (projection F C) D = inner ℝ C (projection F D) := by
  rw [coefficient_inner, coefficient_inner]
  simp_rw [projection_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab _
  apply Finset.sum_congr rfl
  intro cd _
  simp only [real_inner_comm]
  ring

theorem projection_range (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) :
    Set.range (projection F) = Set.range (encode F) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨C, rfl⟩
    exact ⟨decode F C, rfl⟩
  · rintro _ ⟨h, rfl⟩
    exact ⟨encode F h, projection_encode F hF h⟩

theorem projection_norm_le (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) (C : Coefficients iota) :
    ‖projection F C‖ ≤ ‖C‖ := by
  have heq : ‖projection F C‖ ^ 2 = inner ℝ C (projection F C) := by
    rw [← real_inner_self_eq_norm_sq, projection_selfadjoint, projection_idempotent F hF]
  have hbound := real_inner_le_norm C (projection F C)
  by_cases hzero : ‖projection F C‖ = 0
  · rw [hzero]
    exact norm_nonneg C
  · have hpos : 0 < ‖projection F C‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

theorem projection_opNorm_le_one (F : iota → V)
    (hF : ∀ v : V, (∑ a, inner ℝ (F a) v • F a) = v) : ‖projection F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro C
  simpa only [one_mul] using projection_norm_le F hF C

theorem decode_symmetric (F : iota → V) (C : Coefficients iota)
    (hC : ∀ a b, C (a, b) = C (b, a)) (v w : V) :
    decode F C v w = decode F C w v := by
  rw [decode_apply, decode_apply, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hC b a]
  ring

end LinearAlgebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

def nativeDecode (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) (x : M)
    (C : Coefficients iota) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  decode (fun a => F a x) C

theorem nativeDecode_apply (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) (x : M)
    (C : Coefficients iota) (v w : TangentSpace (𝓡 n) x) :
    nativeDecode g F x C v w = ∑ ab : iota × iota,
      C ab * g.inner x (F ab.1 x) v * g.inner x (F ab.2 x) w := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact decode_apply (fun a => F a x) C v w

theorem nativeDecode_probes (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (h : TensorProbeNative.SmoothTensor (n := n) (M := M)) (x : M) :
    nativeDecode g F x (TensorProbeNative.probes F h x) = h x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact decode_encode (fun a => F a x) (hF x) (h x)

def nativeProjection (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) (x : M) :
    Coefficients iota →L[ℝ] Coefficients iota :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  projection (fun a => F a x)

theorem nativeProjection_apply (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M)) (x : M)
    (C : Coefficients iota) (a b : iota) :
    nativeProjection g F x C (a, b) = nativeDecode g F x C (F a x) (F b x) := rfl

theorem nativeProjection_probes (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (h : TensorProbeNative.SmoothTensor (n := n) (M := M)) (x : M) :
    nativeProjection g F x (TensorProbeNative.probes F h x) = TensorProbeNative.probes F h x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact projection_encode (fun a => F a x) (hF x) (h x)

theorem nativeProjection_opNorm_le_one (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ a, g.inner x (F a x) v • F a x) = v)
    (x : M) : ‖nativeProjection g F x‖ ≤ 1 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact projection_opNorm_le_one (fun a => F a x) (hF x)

end PoincareConjecture.ParsevalTensorNative

end
