import PoincareConjecture.Proofs.M03.Existence.TensorHilbertNative










set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.TensorHilbertNative

open TensorProbeNative ParsevalTensorNative HilbertResolventNative

section LpIsometry

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)

private def liftLpEquiv (e : E ≃ₗᵢ[ℝ] E) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 μ := by
  let A := e.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ
  let B := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 μ
  refine {
    toFun := A
    invFun := B
    left_inv := ?_
    right_inv := ?_
    map_add' := map_add A
    map_smul' := fun c f => map_smul A c f
    norm_map' := ?_
  }
  · intro f
    apply Lp.ext
    filter_upwards [e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL (A f),
      e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f] with x hx hy
    rw [hx, hy]
    exact e.symm_apply_apply (f x)
  · intro f
    apply Lp.ext
    filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL (B f),
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f] with x hx hy
    rw [hx, hy]
    exact e.apply_symm_apply (f x)
  · intro f
    change ‖A f‖ = ‖f‖
    apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
    · filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f] with x hx
      rw [hx]
      exact (e.norm_map (f x)).le
    · filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f] with x hx
      rw [hx]
      exact (e.norm_map (f x)).ge

private theorem liftLpEquiv_coe (e : E ≃ₗᵢ[ℝ] E) (f : Lp E 2 μ) :
    liftLpEquiv μ e f =ᵐ[μ] fun x => e (f x) :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

private theorem liftLpEquiv_involutive (e : E ≃ₗᵢ[ℝ] E)
    (he : Function.Involutive e) : Function.Involutive (liftLpEquiv μ e) := by
  intro f
  apply Lp.ext
  filter_upwards [liftLpEquiv_coe μ e (liftLpEquiv μ e f), liftLpEquiv_coe μ e f]
    with x hx hy
  rw [hx, hy]
  exact he (f x)

end LpIsometry

section CoefficientTransposition

variable (iota : Type v) [Fintype iota]

def coefficientTranspose : Coefficients iota ≃ₗᵢ[ℝ] Coefficients iota :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodComm iota iota)

@[simp] theorem coefficientTranspose_apply (c : Coefficients iota) (a b : iota) :
    coefficientTranspose iota c (a, b) = c (b, a) := rfl

theorem coefficientTranspose_involutive : Function.Involutive (coefficientTranspose iota) := by
  intro c
  apply PiLp.ext
  rintro ⟨a, b⟩
  rfl

def derivativeTranspose : DerivativeCoefficients iota ≃ₗᵢ[ℝ] DerivativeCoefficients iota :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr (Equiv.refl iota) (Equiv.prodComm iota iota))

@[simp] theorem derivativeTranspose_apply (c : DerivativeCoefficients iota) (i a b : iota) :
    derivativeTranspose iota c (i, a, b) = c (i, b, a) := rfl

theorem derivativeTranspose_involutive : Function.Involutive (derivativeTranspose iota) := by
  intro c
  apply PiLp.ext
  rintro ⟨i, a, b⟩
  rfl

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def coefficientTransposeL2 : Lp (Coefficients iota) 2 μ ≃ₗᵢ[ℝ] Lp (Coefficients iota) 2 μ :=
  liftLpEquiv μ (coefficientTranspose iota)

theorem coefficientTransposeL2_coe (f : Lp (Coefficients iota) 2 μ) :
    coefficientTransposeL2 iota μ f =ᵐ[μ] fun x => coefficientTranspose iota (f x) :=
  liftLpEquiv_coe μ (coefficientTranspose iota) f

theorem coefficientTransposeL2_involutive : Function.Involutive (coefficientTransposeL2 iota μ) :=
  liftLpEquiv_involutive μ _ (coefficientTranspose_involutive iota)

def derivativeTransposeL2 :
    Lp (DerivativeCoefficients iota) 2 μ ≃ₗᵢ[ℝ] Lp (DerivativeCoefficients iota) 2 μ :=
  liftLpEquiv μ (derivativeTranspose iota)

theorem derivativeTransposeL2_coe (f : Lp (DerivativeCoefficients iota) 2 μ) :
    derivativeTransposeL2 iota μ f =ᵐ[μ] fun x => derivativeTranspose iota (f x) :=
  liftLpEquiv_coe μ (derivativeTranspose iota) f

theorem derivativeTransposeL2_involutive : Function.Involutive (derivativeTransposeL2 iota μ) :=
  liftLpEquiv_involutive μ _ (derivativeTranspose_involutive iota)

end CoefficientTransposition

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Data

variable {g : RiemannianMetric n M} (d : Data g)


def transposeSmooth (h : SmoothTensor (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) :=
  smoothDecode g d.fields
    (fun x => coefficientTranspose (Fin d.fieldCount) (probes d.fields h x))
    (fun ab => contMDiff_pairing h (d.fields ab.2) (d.fields ab.1))

@[simp] theorem transposeSmooth_apply (h : SmoothTensor (n := n) (M := M))
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    d.transposeSmooth h x v w = h x w v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have heq : coefficientTranspose (Fin d.fieldCount) (probes d.fields h x) =
      encode (fun a => d.fields a x) (h x).flip := by
    apply PiLp.ext
    rintro ⟨a, b⟩
    rfl
  change decode (fun a => d.fields a x)
    (coefficientTranspose (Fin d.fieldCount) (probes d.fields h x)) v w = _
  rw [heq, decode_encode (fun a => d.fields a x) (d.parseval x)]
  rfl

theorem coefficientTransposeL2_tensorToLp (h : SmoothTensor (n := n) (M := M)) :
    coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure
        (tensorToLp d.fields d.charts.measure h) =
      tensorToLp d.fields d.charts.measure (d.transposeSmooth h) := by
  apply Lp.ext
  filter_upwards [coefficientTransposeL2_coe (Fin d.fieldCount) d.charts.measure
      (tensorToLp d.fields d.charts.measure h), tensorToLp_coe d.fields d.charts.measure h,
    tensorToLp_coe d.fields d.charts.measure (d.transposeSmooth h)] with x ht hh htranspose
  rw [ht, hh, htranspose]
  apply PiLp.ext
  rintro ⟨a, b⟩
  exact (d.transposeSmooth_apply h x (d.fields a x) (d.fields b x)).symm

theorem derivativeTransposeL2_derivativeToLp (h : SmoothTensor (n := n) (M := M)) :
    derivativeTransposeL2 (Fin d.fieldCount) d.charts.measure
        (derivativeToLp d.fields d.charts.measure h) =
      derivativeToLp d.fields d.charts.measure (d.transposeSmooth h) := by
  apply Lp.ext
  filter_upwards [derivativeTransposeL2_coe (Fin d.fieldCount) d.charts.measure
      (derivativeToLp d.fields d.charts.measure h), derivativeToLp_coe d.fields d.charts.measure h,
    derivativeToLp_coe d.fields d.charts.measure (d.transposeSmooth h)] with x ht hh htranspose
  rw [ht, hh, htranspose]
  apply PiLp.ext
  rintro ⟨i, a, b⟩
  have hfun : (fun y => h y (d.fields b y) (d.fields a y)) =
      (fun y => d.transposeSmooth h y (d.fields a y) (d.fields b y)) := by
    funext y
    exact (d.transposeSmooth_apply h y (d.fields a y) (d.fields b y)).symm
  exact congrArg (fun q : M → ℝ =>
    (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x (d.fields i x) : ℝ)) hfun

theorem coefficientTransposeL2_mem_value (v : d.Value) :
    coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure
      (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) ∈
        tensorL2 d.fields d.charts.measure := by
  refine (intoTensorL2_denseRange d.fields d.charts.measure).induction_on v ?_ ?_
  · exact (tensorToLp d.fields d.charts.measure).range.isClosed_topologicalClosure.preimage
      ((coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure).continuous.comp
        continuous_subtype_val)
  · intro h
    change coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure
        (tensorToLp d.fields d.charts.measure h) ∈ _
    rw [d.coefficientTransposeL2_tensorToLp h]
    exact (intoTensorL2 d.fields d.charts.measure (d.transposeSmooth h)).property


def valueTranspose : d.Value ≃ₗᵢ[ℝ] d.Value where
  toFun v := ⟨coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure v,
    d.coefficientTransposeL2_mem_value v⟩
  invFun v := ⟨coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure v,
    d.coefficientTransposeL2_mem_value v⟩
  left_inv v := Subtype.ext (coefficientTransposeL2_involutive (Fin d.fieldCount) d.charts.measure v)
  right_inv v := Subtype.ext (coefficientTransposeL2_involutive (Fin d.fieldCount) d.charts.measure v)
  map_add' v w := Subtype.ext (map_add (coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure)
    (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure)
    (w : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure))
  map_smul' c v := Subtype.ext (map_smul (coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure)
    c (v : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure))
  norm_map' v := (coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure).norm_map v

theorem valueTranspose_involutive : Function.Involutive d.valueTranspose :=
  d.valueTranspose.left_inv

@[simp] theorem valueTranspose_into (h : SmoothTensor (n := n) (M := M)) :
    d.valueTranspose (intoTensorL2 d.fields d.charts.measure h) =
      intoTensorL2 d.fields d.charts.measure (d.transposeSmooth h) :=
  Subtype.ext (d.coefficientTransposeL2_tensorToLp h)

def ambientTranspose : FirstOrderAmbient d.fields d.charts.measure ≃ₗᵢ[ℝ]
    FirstOrderAmbient d.fields d.charts.measure :=
  d.valueTranspose.withLpProdCongr 2
    (derivativeTransposeL2 (Fin d.fieldCount) d.charts.measure)

theorem ambientTranspose_involutive : Function.Involutive d.ambientTranspose := by
  intro z
  apply (WithLp.equiv 2 (d.Value × Lp (DerivativeCoefficients (Fin d.fieldCount)) 2
    d.charts.measure)).injective
  apply Prod.ext
  · exact d.valueTranspose_involutive z.fst
  · exact derivativeTransposeL2_involutive (Fin d.fieldCount) d.charts.measure z.snd

@[simp] theorem ambientTranspose_firstOrderImage (h : SmoothTensor (n := n) (M := M)) :
    d.ambientTranspose (firstOrderImage d.fields d.charts.measure h) =
      firstOrderImage d.fields d.charts.measure (d.transposeSmooth h) := by
  apply (WithLp.equiv 2 (d.Value × Lp (DerivativeCoefficients (Fin d.fieldCount)) 2
    d.charts.measure)).injective
  apply Prod.ext
  · exact d.valueTranspose_into h
  · exact d.derivativeTransposeL2_derivativeToLp h

theorem ambientTranspose_mem_form (v : d.Form) :
    d.ambientTranspose (v : FirstOrderAmbient d.fields d.charts.measure) ∈
      firstOrderGraph d.fields d.charts.measure := by
  refine (intoFirstOrderGraph_denseRange d.fields d.charts.measure).induction_on v ?_ ?_
  · exact (firstOrderImage d.fields d.charts.measure).range.isClosed_topologicalClosure.preimage
      (d.ambientTranspose.continuous.comp continuous_subtype_val)
  · intro h
    change d.ambientTranspose (firstOrderImage d.fields d.charts.measure h) ∈ _
    rw [d.ambientTranspose_firstOrderImage h]
    exact (intoFirstOrderGraph d.fields d.charts.measure (d.transposeSmooth h)).property

def formTranspose : d.Form ≃ₗᵢ[ℝ] d.Form where
  toFun v := ⟨d.ambientTranspose v, d.ambientTranspose_mem_form v⟩
  invFun v := ⟨d.ambientTranspose v, d.ambientTranspose_mem_form v⟩
  left_inv v := Subtype.ext (d.ambientTranspose_involutive v)
  right_inv v := Subtype.ext (d.ambientTranspose_involutive v)
  map_add' v w := Subtype.ext (map_add d.ambientTranspose
    (v : FirstOrderAmbient d.fields d.charts.measure) (w : FirstOrderAmbient d.fields d.charts.measure))
  map_smul' c v := Subtype.ext (map_smul d.ambientTranspose c
    (v : FirstOrderAmbient d.fields d.charts.measure))
  norm_map' v := d.ambientTranspose.norm_map v

theorem formTranspose_involutive : Function.Involutive d.formTranspose := d.formTranspose.left_inv

@[simp] theorem inclusion_formTranspose (v : d.Form) :
    d.inclusion (d.formTranspose v) = d.valueTranspose (d.inclusion v) := rfl

theorem valueTranspose_inner (v w : d.Value) :
    inner ℝ (d.valueTranspose v) w = inner ℝ v (d.valueTranspose w) := by
  have h := d.valueTranspose.inner_map_map v (d.valueTranspose w)
  rwa [d.valueTranspose_involutive] at h

theorem formTranspose_inner (v w : d.Form) :
    inner ℝ (d.formTranspose v) w = inner ℝ v (d.formTranspose w) := by
  have h := LinearIsometryEquiv.inner_map_map (𝕜 := ℝ)
    (E := firstOrderGraph d.fields d.charts.measure)
    (E' := firstOrderGraph d.fields d.charts.measure) d.formTranspose v (d.formTranspose w)
  rwa [d.formTranspose_involutive] at h


theorem formTranspose_solution (f : d.Value) :
    d.formTranspose (solution d.inclusion f) = solution d.inclusion (d.valueTranspose f) := by
  apply solution_unique (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
    (d.valueTranspose f)
  intro z
  have htranspose := d.formTranspose_inner z
    (solution (V := firstOrderGraph d.fields d.charts.measure)
      (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure) f)
  have hsolution := solution_pairing (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure)
    f (d.formTranspose z)
  change inner ℝ z (d.formTranspose
      (solution (V := firstOrderGraph d.fields d.charts.measure)
        (H := tensorL2 d.fields d.charts.measure) (graphValue d.fields d.charts.measure) f)) =
    inner ℝ (graphValue d.fields d.charts.measure z) (d.valueTranspose f)
  rw [← htranspose, hsolution]
  change inner ℝ (d.inclusion (d.formTranspose z)) f =
    inner ℝ (d.inclusion z) (d.valueTranspose f)
  rw [d.inclusion_formTranspose]
  exact d.valueTranspose_inner _ _

theorem valueTranspose_resolvent (f : d.Value) :
    d.valueTranspose (d.resolvent f) = d.resolvent (d.valueTranspose f) := by
  change d.valueTranspose (d.inclusion (solution d.inclusion f)) =
    d.inclusion (solution d.inclusion (d.valueTranspose f))
  rw [← d.inclusion_formTranspose, d.formTranspose_solution]

end Data

section OrthogonalProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def involutionProjection (e : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ E + e.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem involutionProjection_apply (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    involutionProjection e x = (1 / 2 : ℝ) • (x + e x) := rfl

private theorem involutionProjection_transpose (e : E ≃ₗᵢ[ℝ] E)
    (he : Function.Involutive e) (x : E) : e (involutionProjection e x) = involutionProjection e x := by
  rw [involutionProjection_apply, map_smul, map_add, he, add_comm]

private theorem involutionProjection_eq_self_iff (e : E ≃ₗᵢ[ℝ] E)
    (x : E) : involutionProjection e x = x ↔ e x = x := by
  constructor
  · intro hx
    have h := congrArg (fun z : E => (2 : ℝ) • z) hx
    rw [involutionProjection_apply, smul_smul] at h
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, two_smul] at h
    exact add_left_cancel h
  · intro hx
    rw [involutionProjection_apply, hx, ← two_smul ℝ x, smul_smul]
    norm_num

private theorem involutionProjection_idempotent (e : E ≃ₗᵢ[ℝ] E)
    (he : Function.Involutive e) (x : E) :
    involutionProjection e (involutionProjection e x) = involutionProjection e x :=
  (involutionProjection_eq_self_iff e _).mpr (involutionProjection_transpose e he x)

private theorem norm_involutionProjection_le (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    ‖involutionProjection e x‖ ≤ ‖x‖ := by
  rw [involutionProjection_apply, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := norm_add_le x (e x)
  rw [e.norm_map] at h
  linarith

private theorem involutionProjection_inner (e : E ≃ₗᵢ[ℝ] E)
    (he : Function.Involutive e) (x y : E) :
    inner ℝ (involutionProjection e x) y = inner ℝ x (involutionProjection e y) := by
  have h : inner ℝ (e x) y = inner ℝ x (e y) := by
    have h' := e.inner_map_map x (e y)
    rwa [he] at h'
  rw [involutionProjection_apply, involutionProjection_apply, inner_smul_left,
    inner_smul_right, inner_add_left, inner_add_right, h]
  simp

end OrthogonalProjection

namespace Data

variable {g : RiemannianMetric n M} (d : Data g)

def valueSymmetrize : d.Value →L[ℝ] d.Value := involutionProjection d.valueTranspose

def formSymmetrize : d.Form →L[ℝ] d.Form :=
  involutionProjection (E := firstOrderGraph d.fields d.charts.measure) d.formTranspose

@[simp] theorem valueSymmetrize_apply (x : d.Value) :
    d.valueSymmetrize x = (1 / 2 : ℝ) • (x + d.valueTranspose x) := rfl

@[simp] theorem formSymmetrize_apply (x : d.Form) :
    d.formSymmetrize x = (1 / 2 : ℝ) • (x + d.formTranspose x) := rfl

theorem valueSymmetrize_idempotent (x : d.Value) :
    d.valueSymmetrize (d.valueSymmetrize x) = d.valueSymmetrize x :=
  involutionProjection_idempotent d.valueTranspose d.valueTranspose_involutive x

theorem formSymmetrize_idempotent (x : d.Form) :
    d.formSymmetrize (d.formSymmetrize x) = d.formSymmetrize x := by
  dsimp only [formSymmetrize]
  apply involutionProjection_idempotent (E := firstOrderGraph d.fields d.charts.measure)
    d.formTranspose d.formTranspose_involutive x

theorem norm_valueSymmetrize_le (x : d.Value) : ‖d.valueSymmetrize x‖ ≤ ‖x‖ :=
  norm_involutionProjection_le d.valueTranspose x

theorem norm_formSymmetrize_le (x : d.Form) : ‖d.formSymmetrize x‖ ≤ ‖x‖ := by
  dsimp only [formSymmetrize]
  apply norm_involutionProjection_le (E := firstOrderGraph d.fields d.charts.measure) d.formTranspose x

theorem valueSymmetrize_inner (x y : d.Value) :
    inner ℝ (d.valueSymmetrize x) y = inner ℝ x (d.valueSymmetrize y) :=
  involutionProjection_inner d.valueTranspose d.valueTranspose_involutive x y

theorem formSymmetrize_inner (x y : d.Form) :
    inner ℝ (d.formSymmetrize x) y = inner ℝ x (d.formSymmetrize y) := by
  dsimp only [formSymmetrize]
  apply involutionProjection_inner (E := firstOrderGraph d.fields d.charts.measure)
    d.formTranspose d.formTranspose_involutive x y


def symmetricValue : Submodule ℝ d.Value :=
  (d.valueTranspose.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ d.Value).ker

theorem mem_symmetricValue_iff (x : d.Value) : x ∈ d.symmetricValue ↔ d.valueTranspose x = x := by
  change d.valueTranspose x - x = 0 ↔ d.valueTranspose x = x
  exact sub_eq_zero

theorem isClosed_symmetricValue : IsClosed (d.symmetricValue : Set d.Value) := by
  exact (d.valueTranspose.toContinuousLinearEquiv.toContinuousLinearMap -
    ContinuousLinearMap.id ℝ d.Value).isClosed_ker

theorem valueSymmetrize_mem (x : d.Value) : d.valueSymmetrize x ∈ d.symmetricValue :=
  (d.mem_symmetricValue_iff _).mpr
    (involutionProjection_transpose d.valueTranspose d.valueTranspose_involutive x)

theorem valueSymmetrize_eq_self_of_mem {x : d.Value} (hx : x ∈ d.symmetricValue) :
    d.valueSymmetrize x = x :=
  (involutionProjection_eq_self_iff d.valueTranspose x).mpr ((d.mem_symmetricValue_iff x).mp hx)

theorem range_valueSymmetrize : d.valueSymmetrize.toLinearMap.range = d.symmetricValue := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact d.valueSymmetrize_mem y
  · intro hx
    exact ⟨x, d.valueSymmetrize_eq_self_of_mem hx⟩

theorem valueSymmetrize_residual_orthogonal (x y : d.Value) (hy : y ∈ d.symmetricValue) :
    inner ℝ (x - d.valueSymmetrize x) y = 0 := by
  rw [inner_sub_left, d.valueSymmetrize_inner, d.valueSymmetrize_eq_self_of_mem hy, sub_self]

theorem inclusion_formSymmetrize (x : d.Form) :
    d.inclusion (d.formSymmetrize x) = d.valueSymmetrize (d.inclusion x) := by
  rw [formSymmetrize_apply, map_smul, map_add, d.inclusion_formTranspose, valueSymmetrize_apply]

theorem valueSymmetrize_resolvent (x : d.Value) :
    d.valueSymmetrize (d.resolvent x) = d.resolvent (d.valueSymmetrize x) := by
  rw [valueSymmetrize_apply, valueSymmetrize_apply, map_smul, map_add, d.valueTranspose_resolvent]


theorem generatorGraph_valueSymmetrize {x a : d.Value} (ha : d.GeneratorGraph x a) :
    d.GeneratorGraph (d.valueSymmetrize x) (d.valueSymmetrize a) := by
  change d.resolvent (d.valueSymmetrize x + d.valueSymmetrize a) = d.valueSymmetrize x
  rw [← map_add, ← d.valueSymmetrize_resolvent]
  change d.resolvent (x + a) = x at ha
  rw [ha]

def symmetricForm : Submodule ℝ d.Form :=
  (d.formTranspose.toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ d.Form).ker

theorem mem_symmetricForm_iff (x : d.Form) : x ∈ d.symmetricForm ↔ d.formTranspose x = x := by
  change d.formTranspose x - x = 0 ↔ d.formTranspose x = x
  exact sub_eq_zero

theorem isClosed_symmetricForm : IsClosed (d.symmetricForm : Set d.Form) :=
  (d.formTranspose.toContinuousLinearEquiv.toContinuousLinearMap -
    ContinuousLinearMap.id ℝ d.Form).isClosed_ker

abbrev SymmetricValue := ↥d.symmetricValue

abbrev SymmetricForm := ↥d.symmetricForm

instance symmetricForm_innerProductSpace : InnerProductSpace ℝ d.SymmetricForm :=
  Submodule.innerProductSpace (𝕜 := ℝ)
    (E := firstOrderGraph d.fields d.charts.measure) d.symmetricForm

instance symmetricValue_completeSpace : CompleteSpace d.SymmetricValue :=
  d.isClosed_symmetricValue.isComplete.completeSpace_coe

instance symmetricForm_completeSpace : CompleteSpace d.SymmetricForm :=
  d.isClosed_symmetricForm.isComplete.completeSpace_coe

theorem formSymmetrize_mem (x : d.Form) : d.formSymmetrize x ∈ d.symmetricForm :=
  (d.mem_symmetricForm_iff _).mpr
    (involutionProjection_transpose (E := firstOrderGraph d.fields d.charts.measure)
      d.formTranspose d.formTranspose_involutive x)

theorem formSymmetrize_eq_self_of_mem {x : d.Form} (hx : x ∈ d.symmetricForm) :
    d.formSymmetrize x = x := by
  dsimp only [formSymmetrize]
  apply (involutionProjection_eq_self_iff (E := firstOrderGraph d.fields d.charts.measure)
    d.formTranspose x).mpr
  exact (d.mem_symmetricForm_iff x).mp hx

theorem inclusion_mem_symmetricValue (x : d.SymmetricForm) :
    d.inclusion (x : d.Form) ∈ d.symmetricValue := by
  apply (d.mem_symmetricValue_iff _).mpr
  rw [← d.inclusion_formTranspose, (d.mem_symmetricForm_iff _).mp x.property]


def symmetricInclusion : d.SymmetricForm →L[ℝ] d.SymmetricValue :=
  (d.inclusion.comp d.symmetricForm.subtypeL).codRestrict d.symmetricValue
    d.inclusion_mem_symmetricValue

@[simp] theorem symmetricInclusion_coe (x : d.SymmetricForm) :
    (d.symmetricInclusion x : d.Value) = d.inclusion (x : d.Form) := rfl

theorem symmetricInclusion_injective : Function.Injective d.symmetricInclusion := by
  intro x y hxy
  apply Subtype.ext
  apply d.inclusion_injective
  exact congrArg (fun z : d.SymmetricValue => (z : d.Value)) hxy

theorem symmetricInclusion_compact : IsCompactOperator d.symmetricInclusion :=
  (d.inclusion_compact.comp_clm d.symmetricForm.subtypeL).codRestrict
    d.inclusion_mem_symmetricValue d.isClosed_symmetricValue

theorem norm_symmetricInclusion_le_one : ‖d.symmetricInclusion‖ ≤ 1 := by
  apply d.symmetricInclusion.opNorm_le_bound zero_le_one
  intro x
  change ‖d.inclusion (x : d.Form)‖ ≤ 1 * ‖(x : d.Form)‖
  rw [one_mul]
  exact norm_graphValue_le d.fields d.charts.measure (x : d.Form)


theorem symmetricInclusion_denseRange : DenseRange d.symmetricInclusion := by
  let P : d.Value →L[ℝ] d.SymmetricValue :=
    d.valueSymmetrize.codRestrict d.symmetricValue d.valueSymmetrize_mem
  have hP : Function.Surjective P := by
    intro x
    exact ⟨(x : d.Value), Subtype.ext (d.valueSymmetrize_eq_self_of_mem x.property)⟩
  have hPJ : DenseRange (fun x : d.Form => P (d.inclusion x)) :=
    hP.denseRange.comp d.inclusion_denseRange P.continuous
  apply hPJ.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨d.formSymmetrize x, d.formSymmetrize_mem x⟩,
    Subtype.ext (d.inclusion_formSymmetrize x)⟩

def symmetricResolvent : d.SymmetricValue →L[ℝ] d.SymmetricValue :=
  operator (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion


theorem symmetricSolution_coe (f : d.SymmetricValue) :
    ((solution (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion f : d.SymmetricForm) : d.Form) =
        solution (V := firstOrderGraph d.fields d.charts.measure)
          (H := tensorL2 d.fields d.charts.measure) d.inclusion (f : d.Value) := by
  have hfixed : solution (V := firstOrderGraph d.fields d.charts.measure)
      (H := tensorL2 d.fields d.charts.measure) d.inclusion (f : d.Value) ∈ d.symmetricForm := by
    apply (d.mem_symmetricForm_iff _).mpr
    rw [d.formTranspose_solution, (d.mem_symmetricValue_iff _).mp f.property]
  let u : d.SymmetricForm := ⟨solution (V := firstOrderGraph d.fields d.charts.measure)
    (H := tensorL2 d.fields d.charts.measure) d.inclusion (f : d.Value), hfixed⟩
  have hu : u = solution (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion f := by
    apply solution_unique (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion f u
    intro z
    have hpair := solution_pairing (V := firstOrderGraph d.fields d.charts.measure)
      (H := tensorL2 d.fields d.charts.measure) d.inclusion (f : d.Value) (z : d.Form)
    change inner ℝ (z : d.Form) (u : d.Form) =
      inner ℝ (d.inclusion (z : d.Form)) (f : d.Value)
    exact hpair
  exact congrArg (fun z : d.SymmetricForm => (z : d.Form)) hu.symm

theorem symmetricResolvent_coe (f : d.SymmetricValue) :
    (d.symmetricResolvent f : d.Value) = d.resolvent (f : d.Value) := by
  change d.inclusion ((solution (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion f : d.SymmetricForm) : d.Form) =
    d.inclusion (solution (V := firstOrderGraph d.fields d.charts.measure)
      (H := tensorL2 d.fields d.charts.measure) d.inclusion (f : d.Value))
  rw [d.symmetricSolution_coe]

def SymmetricGeneratorGraph (x a : d.SymmetricValue) : Prop :=
  InGeneratorGraph (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion x a

theorem symmetricGeneratorGraph_iff (x a : d.SymmetricValue) :
    d.SymmetricGeneratorGraph x a ↔ d.GeneratorGraph (x : d.Value) (a : d.Value) := by
  constructor
  · intro h
    change d.symmetricResolvent (x + a) = x at h
    have hc := congrArg (fun z : d.SymmetricValue => (z : d.Value)) h
    change (d.symmetricResolvent (x + a) : d.Value) = (x : d.Value) at hc
    rw [d.symmetricResolvent_coe] at hc
    exact hc
  · intro h
    change d.symmetricResolvent (x + a) = x
    apply Subtype.ext
    change (d.symmetricResolvent (x + a) : d.Value) = (x : d.Value)
    rw [d.symmetricResolvent_coe]
    exact h

abbrev SymmetricIndex :=
  EigenIndex (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion

def symmetricBasis : HilbertBasis d.SymmetricIndex ℝ d.SymmetricValue := by
  apply eigenbasis (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
  · exact d.symmetricInclusion_compact
  · exact d.symmetricInclusion_denseRange

def symmetricParameters : d.SymmetricIndex → NNReal := by
  apply generatorParameters (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
  · exact d.symmetricInclusion_compact
  · exact d.symmetricInclusion_denseRange
  · exact d.norm_symmetricInclusion_le_one


def symmetricScaleValue (k : ℕ) : SpectralHeatNative.State d.SymmetricIndex →L[ℝ] d.SymmetricValue := by
  apply scaleValue (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion (k := k)
  · exact d.symmetricInclusion_compact
  · exact d.symmetricInclusion_denseRange
  · exact d.norm_symmetricInclusion_le_one

theorem norm_symmetricScaleValue_le (k : ℕ) (x : SpectralHeatNative.State d.SymmetricIndex) :
    ‖d.symmetricScaleValue k x‖ ≤ ‖x‖ := by
  change ‖d.symmetricBasis.repr.symm
    (SpectralHeatNative.scaleDecode d.symmetricParameters k x)‖ ≤ ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  exact SpectralHeatNative.norm_scaleDecode_le d.symmetricParameters k x

theorem symmetricScaleValue_injective (k : ℕ) : Function.Injective (d.symmetricScaleValue k) := by
  intro x y hxy
  change d.symmetricBasis.repr.symm (SpectralHeatNative.scaleDecode d.symmetricParameters k x) =
    d.symmetricBasis.repr.symm (SpectralHeatNative.scaleDecode d.symmetricParameters k y) at hxy
  apply SpectralHeatNative.scaleDecode_injective d.symmetricParameters k
  exact d.symmetricBasis.repr.symm.injective hxy


theorem symmetricValue_coefficients (u : d.SymmetricValue) :
    ∀ᵐ x ∂d.charts.measure, ∀ a b : Fin d.fieldCount,
      ((u : d.Value) : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x (a, b) =
        ((u : d.Value) : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x (b, a) := by
  have hfix := congrArg
    (fun z : d.Value => (z : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure))
    ((d.mem_symmetricValue_iff _).mp u.property)
  change coefficientTransposeL2 (Fin d.fieldCount) d.charts.measure
      ((u : d.Value) : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) =
    ((u : d.Value) : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) at hfix
  have hcoe := coefficientTransposeL2_coe (Fin d.fieldCount) d.charts.measure
    ((u : d.Value) : Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure)
  rw [hfix] at hcoe
  filter_upwards [hcoe] with x hx
  intro a b
  exact congrArg (fun z : Coefficients (Fin d.fieldCount) => z (a, b)) hx

theorem symmetricScaleValue_coefficients (k : ℕ) (u : SpectralHeatNative.State d.SymmetricIndex) :
    ∀ᵐ x ∂d.charts.measure, ∀ a b : Fin d.fieldCount,
      ((d.symmetricScaleValue k u : d.Value) :
        Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x (a, b) =
      ((d.symmetricScaleValue k u : d.Value) :
        Lp (Coefficients (Fin d.fieldCount)) 2 d.charts.measure) x (b, a) :=
  d.symmetricValue_coefficients (d.symmetricScaleValue k u)

def intoSymmetricValue (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    d.SymmetricValue := by
  refine ⟨intoTensorL2 d.fields d.charts.measure h, ?_⟩
  apply (d.mem_symmetricValue_iff _).mpr
  rw [d.valueTranspose_into]
  have ht : d.transposeSmooth h = h := by
    apply ContMDiffSection.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [d.transposeSmooth_apply, hsymm x w v]
  rw [ht]


theorem symmetricGeneratorGraph_smoothTensorLaplacian
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    d.SymmetricGeneratorGraph (d.intoSymmetricValue h hsymm)
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
        (smoothTensorLaplacian_symm d.fields d.charts g h hsymm)) := by
  apply (d.symmetricGeneratorGraph_iff _ _).mpr
  exact inGeneratorGraph_smoothTensorLaplacian d.fields d.charts g d.parseval h


def shiftedSmoothTensor (h : SmoothTensor (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) :=
  h + smoothTensorLaplacian d.fields d.charts g h

theorem shiftedSmoothTensor_symm (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    d.shiftedSmoothTensor h x v w = d.shiftedSmoothTensor h x w v := by
  change h x v w + smoothTensorLaplacian d.fields d.charts g h x v w =
    h x w v + smoothTensorLaplacian d.fields d.charts g h x w v
  rw [hsymm x v w, smoothTensorLaplacian_symm d.fields d.charts g h hsymm x v w]

def shiftedSmoothPower : ℕ → SmoothTensor (n := n) (M := M) →
    SmoothTensor (n := n) (M := M)
  | 0, h => h
  | k + 1, h => d.shiftedSmoothTensor (shiftedSmoothPower k h)

theorem shiftedSmoothPower_symm (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      d.shiftedSmoothPower k h x v w = d.shiftedSmoothPower k h x w v := by
  induction k with
  | zero => exact hsymm
  | succ k ih => exact d.shiftedSmoothTensor_symm (d.shiftedSmoothPower k h) ih

theorem symmetricBasis_shiftedSmoothTensor (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (i : d.SymmetricIndex) :
    d.symmetricBasis.repr
        (d.intoSymmetricValue (d.shiftedSmoothTensor h) (d.shiftedSmoothTensor_symm h hsymm)) i =
      (1 + (d.symmetricParameters i : ℝ)) *
        d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i := by
  have hgraph := d.symmetricGeneratorGraph_smoothTensorLaplacian h hsymm
  dsimp only [SymmetricGeneratorGraph] at hgraph
  have hcoeff : InGeneratorGraph (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion (d.intoSymmetricValue h hsymm)
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
        (smoothTensorLaplacian_symm d.fields d.charts g h hsymm)) ↔
      ∀ j : d.SymmetricIndex,
        d.symmetricBasis.repr
            (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
              (smoothTensorLaplacian_symm d.fields d.charts g h hsymm)) j =
          (d.symmetricParameters j : ℝ) *
            d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) j := by
    dsimp only [symmetricBasis, symmetricParameters]
    apply inGeneratorGraph_iff_coeff (V := ↥d.symmetricForm) (H := ↥d.symmetricValue)
      d.symmetricInclusion
    all_goals first
      | exact d.symmetricInclusion_compact
      | exact d.symmetricInclusion_denseRange
      | exact d.norm_symmetricInclusion_le_one
  have hlap := hcoeff.mp hgraph i
  change d.symmetricBasis.repr
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
        (smoothTensorLaplacian_symm d.fields d.charts g h hsymm)) i =
    (d.symmetricParameters i : ℝ) * d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i
    at hlap
  have hshift :
      d.intoSymmetricValue (d.shiftedSmoothTensor h) (d.shiftedSmoothTensor_symm h hsymm) =
      d.intoSymmetricValue h hsymm +
        d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
          (smoothTensorLaplacian_symm d.fields d.charts g h hsymm) := by
    apply Subtype.ext
    exact map_add (intoTensorL2 d.fields d.charts.measure) h
      (smoothTensorLaplacian d.fields d.charts g h)
  rw [hshift, map_add]
  change d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i +
    d.symmetricBasis.repr
      (d.intoSymmetricValue (smoothTensorLaplacian d.fields d.charts g h)
        (smoothTensorLaplacian_symm d.fields d.charts g h hsymm)) i = _
  rw [hlap]
  ring

theorem symmetricBasis_shiftedSmoothPower (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (i : d.SymmetricIndex) :
    d.symmetricBasis.repr
        (d.intoSymmetricValue (d.shiftedSmoothPower k h) (d.shiftedSmoothPower_symm k h hsymm)) i =
      (1 + (d.symmetricParameters i : ℝ)) ^ k *
        d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) i := by
  induction k with
  | zero => simp only [shiftedSmoothPower, pow_zero, one_mul]
  | succ k ih =>
    change d.symmetricBasis.repr
      (d.intoSymmetricValue (d.shiftedSmoothTensor (d.shiftedSmoothPower k h))
        (d.shiftedSmoothTensor_symm _ (d.shiftedSmoothPower_symm k h hsymm))) i = _
    rw [d.symmetricBasis_shiftedSmoothTensor (d.shiftedSmoothPower k h)
      (d.shiftedSmoothPower_symm k h hsymm) i, ih, pow_succ]
    ring


theorem scaleDecode_shiftedSmoothPower (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.scaleDecode d.symmetricParameters (2 * k)
      (d.symmetricBasis.repr
        (d.intoSymmetricValue (d.shiftedSmoothPower k h) (d.shiftedSmoothPower_symm k h hsymm))) =
      d.symmetricBasis.repr (d.intoSymmetricValue h hsymm) := by
  apply lp.ext
  funext i
  rw [SpectralHeatNative.scaleDecode_apply, d.symmetricBasis_shiftedSmoothPower]
  have hweight : SpectralHeatNative.scaleWeight d.symmetricParameters (2 * k) i =
      (1 + (d.symmetricParameters i : ℝ)) ^ k := by
    rw [SpectralHeatNative.scaleWeight, pow_mul,
      Real.sq_sqrt (by positivity : 0 ≤ 1 + (d.symmetricParameters i : ℝ))]
  rw [hweight, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem inScale_even_smoothTensor (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.InScale d.symmetricParameters (2 * k)
      (d.symmetricBasis.repr (d.intoSymmetricValue h hsymm)) := by
  rw [SpectralHeatNative.inScale_iff_mem_range]
  exact ⟨d.symmetricBasis.repr
    (d.intoSymmetricValue (d.shiftedSmoothPower k h) (d.shiftedSmoothPower_symm k h hsymm)),
      d.scaleDecode_shiftedSmoothPower k h hsymm⟩

theorem inScale_smoothTensor (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.InScale d.symmetricParameters k
      (d.symmetricBasis.repr (d.intoSymmetricValue h hsymm)) :=
  SpectralHeatNative.inScale_mono d.symmetricParameters (by omega : k ≤ 2 * k)
    (d.inScale_even_smoothTensor k h hsymm)

theorem scaleEncode_even_smoothTensor (k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.scaleEncode d.symmetricParameters (2 * k)
        (d.symmetricBasis.repr (d.intoSymmetricValue h hsymm))
        (d.inScale_even_smoothTensor k h hsymm) =
      d.symmetricBasis.repr
        (d.intoSymmetricValue (d.shiftedSmoothPower k h) (d.shiftedSmoothPower_symm k h hsymm)) := by
  apply SpectralHeatNative.scaleDecode_injective d.symmetricParameters (2 * k)
  rw [SpectralHeatNative.scaleDecode_scaleEncode, d.scaleDecode_shiftedSmoothPower]

def smoothTensorCoordinates (m : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.State d.SymmetricIndex :=
  SpectralHeatNative.scaleEncode d.symmetricParameters m
    (d.symmetricBasis.repr (d.intoSymmetricValue h hsymm)) (d.inScale_smoothTensor m h hsymm)


theorem inScale_smoothTensorCoordinates (m k : ℕ) (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.InScale d.symmetricParameters k (d.smoothTensorCoordinates m h hsymm) := by
  have hs := d.inScale_smoothTensor (k + m) h hsymm
  simpa only [SpectralHeatNative.InScale, smoothTensorCoordinates,
    SpectralHeatNative.scaleEncode_apply, SpectralHeatNative.scaleWeight_add, mul_assoc] using hs

theorem symmetricScaleValue_smoothTensorCoordinates (m : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    d.symmetricScaleValue m (d.smoothTensorCoordinates m h hsymm) =
      d.intoSymmetricValue h hsymm := by
  change d.symmetricBasis.repr.symm
    (SpectralHeatNative.scaleDecode d.symmetricParameters m
      (d.smoothTensorCoordinates m h hsymm)) = _
  rw [smoothTensorCoordinates, SpectralHeatNative.scaleDecode_scaleEncode,
    LinearIsometryEquiv.symm_apply_apply]


theorem smoothTensorCoordinates_even_norm_sq (r : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    ‖d.smoothTensorCoordinates (2 * r) h hsymm‖ ^ 2 =
      ∫ x, ‖probes d.fields (d.shiftedSmoothPower r h) x‖ ^ 2 ∂d.charts.measure := by
  rw [smoothTensorCoordinates, d.scaleEncode_even_smoothTensor,
    LinearIsometryEquiv.norm_map]
  change ‖tensorToLp d.fields d.charts.measure (d.shiftedSmoothPower r h)‖ ^ 2 = _
  exact tensorToLp_norm_sq d.fields d.charts.measure _


def residualCoordinates (m : ℕ) {g' : RiemannianMetric n M}
    (D : LeviCivitaData g') (B : LeviCivitaData g)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.State d.SymmetricIndex :=
  d.smoothTensorCoordinates m (smoothResidualTensor d.fields d.charts D B h)
    (smoothResidualTensor_symm d.fields d.charts D B h hsymm)

theorem symmetricScaleValue_residualCoordinates (m : ℕ) {g' : RiemannianMetric n M}
    (D : LeviCivitaData g') (B : LeviCivitaData g)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    d.symmetricScaleValue m (d.residualCoordinates m D B h hsymm) =
      d.intoSymmetricValue (smoothResidualTensor d.fields d.charts D B h)
        (smoothResidualTensor_symm d.fields d.charts D B h hsymm) :=
  d.symmetricScaleValue_smoothTensorCoordinates m _ _

theorem residualCoordinates_even_norm_sq (r : ℕ) {g' : RiemannianMetric n M}
    (D : LeviCivitaData g') (B : LeviCivitaData g)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    ‖d.residualCoordinates (2 * r) D B h hsymm‖ ^ 2 =
      ∫ x, ‖probes d.fields
        (d.shiftedSmoothPower r (smoothResidualTensor d.fields d.charts D B h)) x‖ ^ 2
          ∂d.charts.measure :=
  d.smoothTensorCoordinates_even_norm_sq r _ _

theorem inScale_residualCoordinates (m k : ℕ) {g' : RiemannianMetric n M}
    (D : LeviCivitaData g') (B : LeviCivitaData g)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    SpectralHeatNative.InScale d.symmetricParameters k (d.residualCoordinates m D B h hsymm) :=
  d.inScale_smoothTensorCoordinates m k _ _


def initialResidualCoordinates (m : ℕ) (B : LeviCivitaData g) :
    SpectralHeatNative.State d.SymmetricIndex :=
  d.residualCoordinates m B B 0 (fun _ _ _ => rfl)

theorem inScale_initialResidualCoordinates (m k : ℕ) (B : LeviCivitaData g) :
    SpectralHeatNative.InScale d.symmetricParameters k (d.initialResidualCoordinates m B) :=
  d.inScale_residualCoordinates m k B B 0 _

variable [SecondCountableTopology M]

instance symmetricValue_separable : TopologicalSpace.SeparableSpace d.SymmetricValue := inferInstance

instance symmetricIndex_countable : Countable d.SymmetricIndex := by
  apply eigenIndex_countable (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
  exact d.symmetricInclusion_compact

end Data

end PoincareConjecture.TensorHilbertNative
