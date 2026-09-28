import PoincareConjecture.Proofs.M03.Existence.NativeChartIntegrationNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorSmoothNative
import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorL2Native
import PoincareConjecture.Proofs.M03.Existence.HilbertParabolicNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckTameRemainderNative
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative










set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

noncomputable section

universe u v

namespace PoincareConjecture.TensorProbeNative

open ChartMeasureNative ParsevalTensorNative HilbertResolventNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {iota : Type v} [Fintype iota]

variable (F : iota → SmoothField (n := n) (M := M))
  (d : FiniteChartData (n := n) (M := M))


def scalarLaplacian (f : M → ℝ) (x : M) : ℝ :=
  ∑ i, d.fieldAdjoint (F i) (scalarDirectional (F i) f) x

theorem scalarLaplacian_contMDiff {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarLaplacian F d f) := by
  classical
  apply contMDiff_finsetSum
  intro i _
  exact d.fieldAdjoint_contMDiff (F i) (contMDiff_directional hf (F i))

def scalarProbe (h : SmoothTensor (n := n) (M := M)) (ab : iota × iota) (x : M) : ℝ :=
  h x (F ab.1 x) (F ab.2 x)

theorem scalarProbe_contMDiff (h : SmoothTensor (n := n) (M := M)) (ab : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarProbe F h ab) :=
  contMDiff_pairing h (F ab.1) (F ab.2)


def rawLaplacianCoefficients (h : SmoothTensor (n := n) (M := M)) (x : M) : Coefficients iota :=
  WithLp.toLp 2 (fun ab : iota × iota => scalarLaplacian F d (scalarProbe F h ab) x)

theorem rawLaplacianCoefficients_contMDiff (h : SmoothTensor (n := n) (M := M))
    (ab : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => rawLaplacianCoefficients F d h x ab) :=
  scalarLaplacian_contMDiff F d (scalarProbe_contMDiff F h ab)


def smoothTensorLaplacian (g : RiemannianMetric n M) (h : SmoothTensor (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) :=
  smoothDecode g F (rawLaplacianCoefficients F d h) (rawLaplacianCoefficients_contMDiff F d h)

theorem probes_smoothTensorLaplacian (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M)) (x : M) :
    probes F (smoothTensorLaplacian F d g h) x =
      nativeProjection g F x (rawLaplacianCoefficients F d h x) :=
  probes_smoothDecode g F (rawLaplacianCoefficients F d h)
    (rawLaplacianCoefficients_contMDiff F d h) x

theorem smoothTensorLaplacian_symm (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    smoothTensorLaplacian F d g h x v w = smoothTensorLaplacian F d g h x w v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply decode_symmetric (fun i => F i x) (rawLaplacianCoefficients F d h x)
  intro a b
  have hp : scalarProbe F h (a, b) = scalarProbe F h (b, a) :=
    funext (fun y => hsymm y (F a y) (F b y))
  change scalarLaplacian F d (scalarProbe F h (a, b)) x =
    scalarLaplacian F d (scalarProbe F h (b, a)) x
  rw [hp]

theorem inner_probes_smoothTensorLaplacian (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (k h : SmoothTensor (n := n) (M := M)) (x : M) :
    inner ℝ (probes F k x) (probes F (smoothTensorLaplacian F d g h) x) =
      inner ℝ (probes F k x) (rawLaplacianCoefficients F d h x) := by
  rw [probes_smoothTensorLaplacian, ← nativeProjection_selfadjoint,
    nativeProjection_probes g F hF k x]

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]


theorem integral_scalarLaplacian_pairing {f η : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η) :
    (∫ x, ∑ i, scalarDirectional (F i) f x * scalarDirectional (F i) η x ∂d.measure) =
      ∫ x, f x * scalarLaplacian F d η x ∂d.measure := by
  classical
  have hleft (i : iota) : Integrable
      (fun x => scalarDirectional (F i) f x * scalarDirectional (F i) η x) d.measure :=
    ((contMDiff_directional hf (F i)).continuous.mul
      (contMDiff_directional hη (F i)).continuous).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact
  have hright (i : iota) : Integrable
      (fun x => f x * d.fieldAdjoint (F i) (scalarDirectional (F i) η) x) d.measure :=
    (hf.continuous.mul (d.fieldAdjoint_contMDiff (F i)
      (contMDiff_directional hη (F i))).continuous).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact
  calc
    _ = ∑ i, ∫ x, scalarDirectional (F i) f x * scalarDirectional (F i) η x ∂d.measure :=
      integral_finsetSum Finset.univ (fun i _ => hleft i)
    _ = ∑ i, ∫ x, f x * d.fieldAdjoint (F i) (scalarDirectional (F i) η) x ∂d.measure :=
      Finset.sum_congr rfl (fun i _ =>
        d.integral_directional_eq_adjoint (F i) hf (contMDiff_directional hη (F i)))
    _ = ∫ x, ∑ i, f x * d.fieldAdjoint (F i) (scalarDirectional (F i) η) x ∂d.measure :=
      (integral_finsetSum Finset.univ (fun i _ => hright i)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => (Finset.mul_sum _ _ _).symm)

theorem inner_derivativeProbes_eq_sum (k h : SmoothTensor (n := n) (M := M)) (x : M) :
    inner ℝ (derivativeProbes F k x) (derivativeProbes F h x) =
      ∑ ab : iota × iota, ∑ i,
        scalarDirectional (F i) (scalarProbe F k ab) x *
          scalarDirectional (F i) (scalarProbe F h ab) x := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab _
  apply Finset.sum_congr rfl
  intro i _
  change scalarDirectional (F i) (scalarProbe F h ab) x *
      scalarDirectional (F i) (scalarProbe F k ab) x = _
  exact mul_comm _ _


theorem integral_derivativeProbes_pairing (k h : SmoothTensor (n := n) (M := M)) :
    (∫ x, inner ℝ (derivativeProbes F k x) (derivativeProbes F h x) ∂d.measure) =
      ∫ x, inner ℝ (probes F k x) (rawLaplacianCoefficients F d h x) ∂d.measure := by
  classical
  have hleft (ab : iota × iota) : Integrable
      (fun x => ∑ i, scalarDirectional (F i) (scalarProbe F k ab) x *
        scalarDirectional (F i) (scalarProbe F h ab) x) d.measure := by
    apply integrable_finsetSum
    intro i _
    exact ((contMDiff_directional (scalarProbe_contMDiff F k ab) (F i)).continuous.mul
      (contMDiff_directional (scalarProbe_contMDiff F h ab) (F i)).continuous).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact
  have hright (ab : iota × iota) : Integrable
      (fun x => scalarProbe F k ab x * scalarLaplacian F d (scalarProbe F h ab) x) d.measure :=
    ((scalarProbe_contMDiff F k ab).continuous.mul
      (scalarLaplacian_contMDiff F d (scalarProbe_contMDiff F h ab)).continuous).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact
  calc
    _ = ∫ x, ∑ ab : iota × iota, ∑ i,
        scalarDirectional (F i) (scalarProbe F k ab) x *
          scalarDirectional (F i) (scalarProbe F h ab) x ∂d.measure :=
      integral_congr_ae (Eventually.of_forall (inner_derivativeProbes_eq_sum F k h))
    _ = ∑ ab : iota × iota, ∫ x, ∑ i,
        scalarDirectional (F i) (scalarProbe F k ab) x *
          scalarDirectional (F i) (scalarProbe F h ab) x ∂d.measure :=
      integral_finsetSum Finset.univ (fun ab _ => hleft ab)
    _ = ∑ ab : iota × iota, ∫ x,
        scalarProbe F k ab x * scalarLaplacian F d (scalarProbe F h ab) x ∂d.measure :=
      Finset.sum_congr rfl (fun ab _ => integral_scalarLaplacian_pairing F d
        (scalarProbe_contMDiff F k ab) (scalarProbe_contMDiff F h ab))
    _ = ∫ x, ∑ ab : iota × iota,
        scalarProbe F k ab x * scalarLaplacian F d (scalarProbe F h ab) x ∂d.measure :=
      (integral_finsetSum Finset.univ (fun ab _ => hright ab)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      exact (coefficient_inner (probes F k x) (rawLaplacianCoefficients F d h x)).symm


theorem derivativeToLp_pairing_laplacian (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (k h : SmoothTensor (n := n) (M := M)) :
    inner ℝ (derivativeToLp F d.measure k) (derivativeToLp F d.measure h) =
      inner ℝ (tensorToLp F d.measure k) (tensorToLp F d.measure (smoothTensorLaplacian F d g h)) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, inner ℝ (derivativeProbes F k x) (derivativeProbes F h x) ∂d.measure := by
      apply integral_congr_ae
      filter_upwards [derivativeToLp_coe F d.measure k, derivativeToLp_coe F d.measure h]
        with x hk hh
      rw [hk, hh]
    _ = ∫ x, inner ℝ (probes F k x) (rawLaplacianCoefficients F d h x) ∂d.measure :=
      integral_derivativeProbes_pairing F d k h
    _ = ∫ x, inner ℝ (probes F k x) (probes F (smoothTensorLaplacian F d g h) x) ∂d.measure :=
      integral_congr_ae (Eventually.of_forall
        (fun x => (inner_probes_smoothTensorLaplacian F d g hF k h x).symm))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [tensorToLp_coe F d.measure k,
        tensorToLp_coe F d.measure (smoothTensorLaplacian F d g h)] with x hk hh
      rw [hk, hh]


theorem form_pairing_laplacian (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M)) (z : firstOrderGraph F d.measure) :
    inner ℝ z (intoFirstOrderGraph F d.measure h) =
      inner ℝ (graphValue F d.measure z)
        (intoTensorL2 F d.measure h + intoTensorL2 F d.measure (smoothTensorLaplacian F d g h)) := by
  have heq : (fun z : firstOrderGraph F d.measure =>
      inner ℝ z (intoFirstOrderGraph F d.measure h)) =
      (fun z : firstOrderGraph F d.measure => inner ℝ (graphValue F d.measure z)
        (intoTensorL2 F d.measure h + intoTensorL2 F d.measure (smoothTensorLaplacian F d g h))) := by
    apply (intoFirstOrderGraph_denseRange F d.measure).equalizer
      (continuous_id.inner continuous_const)
      ((graphValue F d.measure).continuous.inner continuous_const)
    funext k
    simp only [Function.comp_apply]
    change inner ℝ (firstOrderImage F d.measure k) (firstOrderImage F d.measure h) = _
    rw [WithLp.prod_inner_apply, graphValue_into, inner_add_right]
    change inner ℝ (tensorToLp F d.measure k) (tensorToLp F d.measure h) +
        inner ℝ (derivativeToLp F d.measure k) (derivativeToLp F d.measure h) =
      inner ℝ (tensorToLp F d.measure k) (tensorToLp F d.measure h) +
        inner ℝ (tensorToLp F d.measure k)
          (tensorToLp F d.measure (smoothTensorLaplacian F d g h))
    rw [derivativeToLp_pairing_laplacian F d g hF k h]
  exact congrFun heq z


theorem inGeneratorGraph_smoothTensorLaplacian (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M)) :
    InGeneratorGraph (V := firstOrderGraph F d.measure) (H := tensorL2 F d.measure)
      (graphValue F d.measure) (intoTensorL2 F d.measure h)
      (intoTensorL2 F d.measure (smoothTensorLaplacian F d g h)) := by
  apply (inGeneratorGraph_iff_variational (V := firstOrderGraph F d.measure)
    (H := tensorL2 F d.measure) _ _ _).mpr
  exact ⟨intoFirstOrderGraph F d.measure h, rfl, form_pairing_laplacian F d g hF h⟩


theorem inGeneratorGraph_pairing_smooth (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    {u a : tensorL2 F d.measure}
    (ha : InGeneratorGraph (V := firstOrderGraph F d.measure) (H := tensorL2 F d.measure)
      (graphValue F d.measure) u a)
    (k : SmoothTensor (n := n) (M := M)) :
    inner ℝ (intoTensorL2 F d.measure k) a =
      inner ℝ (intoTensorL2 F d.measure (smoothTensorLaplacian F d g k)) u := by
  obtain ⟨z, hz, hpair⟩ :=
    (inGeneratorGraph_iff_variational (V := firstOrderGraph F d.measure)
      (H := tensorL2 F d.measure) (graphValue F d.measure) u a).mp ha
  have hk := hpair (intoFirstOrderGraph F d.measure k)
  have hcore := form_pairing_laplacian F d g hF k z
  rw [graphValue_into, inner_add_right] at hk
  rw [← real_inner_comm z (intoFirstOrderGraph F d.measure k), hz, inner_add_right,
    ← real_inner_comm u (intoTensorL2 F d.measure k),
    ← real_inner_comm u (intoTensorL2 F d.measure (smoothTensorLaplacian F d g k))] at hcore
  exact add_left_cancel (hk.symm.trans hcore)


theorem integral_inGeneratorGraph_pairing_smooth (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    {u a : tensorL2 F d.measure}
    (ha : InGeneratorGraph (V := firstOrderGraph F d.measure) (H := tensorL2 F d.measure)
      (graphValue F d.measure) u a)
    (k : SmoothTensor (n := n) (M := M)) :
    (∫ x, inner ℝ (probes F k x) ((a : Lp (Coefficients iota) 2 d.measure) x) ∂d.measure) =
      ∫ x, inner ℝ (probes F (smoothTensorLaplacian F d g k) x)
        ((u : Lp (Coefficients iota) 2 d.measure) x) ∂d.measure := by
  have h := inGeneratorGraph_pairing_smooth F d g hF ha k
  change inner ℝ (tensorToLp F d.measure k) (a : Lp (Coefficients iota) 2 d.measure) =
    inner ℝ (tensorToLp F d.measure (smoothTensorLaplacian F d g k))
      (u : Lp (Coefficients iota) 2 d.measure) at h
  rw [L2.inner_def, L2.inner_def] at h
  calc
    _ = ∫ x, inner ℝ (tensorToLp F d.measure k x)
        ((a : Lp (Coefficients iota) 2 d.measure) x) ∂d.measure := by
      apply integral_congr_ae
      filter_upwards [tensorToLp_coe F d.measure k] with x hx
      rw [hx]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [tensorToLp_coe F d.measure (smoothTensorLaplacian F d g k)] with x hx
      rw [hx]

section LocalProduct

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M]


theorem contMDiffOn_scalarDirectional {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (V : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarDirectional V f) U := by
  have htan := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn
  have hsec := htan.comp V.contMDiff.contMDiffOn (fun x hx => hx)
  have hproj := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn hsec
  change ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun x => mfderivWithin (𝓡 n) 𝓘(ℝ, ℝ) f U x (V x)) U at hproj
  apply hproj.congr
  intro x hx
  simp only [scalarDirectional, mfderivWithin_of_isOpen hU hx]

private theorem scalarDirectional_add (V : SmoothField (n := n) (M := M))
    {f q : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q x) :
    scalarDirectional V (fun y => f y + q y) x =
      scalarDirectional V f x + scalarDirectional V q x := by
  exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x)) (mfderiv_add hf hq)

private theorem scalarDirectional_finsetSum {jota : Type*} (s : Finset jota)
    (V : SmoothField (n := n) (M := M)) (f : jota → M → ℝ) {x : M}
    (hf : ∀ j ∈ s, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f j) x) :
    scalarDirectional V (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, scalarDirectional V (f j) x := by
  classical
  have hd : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ j ∈ s, f j y) x
      (∑ j ∈ s, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f j) x) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (hasMFDerivAt_const (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (0 : ℝ) x)
    | @insert j s hj ih =>
      have heq : (fun y => ∑ k ∈ insert j s, f k y) =
          (fun y => f j y + ∑ k ∈ s, f k y) := by
        funext y
        exact Finset.sum_insert hj
      rw [heq, Finset.sum_insert hj]
      exact (hf j (Finset.mem_insert_self j s)).hasMFDerivAt.add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
  change (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ j ∈ s, f j y) x) (V x) =
    ∑ j ∈ s, (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f j) x) (V x)
  rw [hd.mfderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rfl


theorem scalarDirectional_twice_mul (V : SmoothField (n := n) (M := M))
    {U : Set M} (hU : IsOpen U) {f q : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) {x : M} (hx : x ∈ U) :
    scalarDirectional V (scalarDirectional V (fun y => f y * q y)) x =
      f x * scalarDirectional V (scalarDirectional V q) x +
        q x * scalarDirectional V (scalarDirectional V f) x +
          2 * scalarDirectional V f x * scalarDirectional V q x := by
  have hDf := contMDiffOn_scalarDirectional hU hf V
  have hDq := contMDiffOn_scalarDirectional hU hq V
  have hfd := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hqd := (hq.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hDfd := (hDf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hDqd := (hDq.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have heq : scalarDirectional V (fun y => f y * q y) =ᶠ[𝓝 x]
      (fun y => f y * scalarDirectional V q y + q y * scalarDirectional V f y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact scalarDirectional_mul V
      ((hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      ((hq.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have houter : scalarDirectional V (scalarDirectional V (fun y => f y * q y)) x =
      scalarDirectional V
        (fun y => f y * scalarDirectional V q y + q y * scalarDirectional V f y) x :=
    congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (V x)) heq.mfderiv_eq
  rw [houter, scalarDirectional_add V
    (f := fun y => f y * scalarDirectional V q y)
    (q := fun y => q y * scalarDirectional V f y) (hfd.mul hDqd) (hqd.mul hDfd),
    scalarDirectional_mul V hfd hDqd, scalarDirectional_mul V hqd hDfd]
  ring


theorem scalarLaplacian_mul {U : Set M} (hU : IsOpen U) {f q : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q U) {x : M} (hx : x ∈ U) :
    scalarLaplacian F d (fun y => f y * q y) x =
      f x * scalarLaplacian F d q x + q x * scalarLaplacian F d f x -
        2 * ∑ i, scalarDirectional (F i) f x * scalarDirectional (F i) q x := by
  classical
  have hfd := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hqd := (hq.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  unfold scalarLaplacian
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold FiniteChartData.fieldAdjoint
  rw [scalarDirectional_twice_mul (F i) hU hf hq hx,
    scalarDirectional_mul (F i) hfd hqd]
  ring

theorem scalarLaplacian_finsetSum {jota : Type*} (s : Finset jota)
    {U : Set M} (hU : IsOpen U) (f : jota → M → ℝ)
    (hf : ∀ j ∈ s, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) U)
    {x : M} (hx : x ∈ U) :
    scalarLaplacian F d (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, scalarLaplacian F d (f j) x := by
  classical
  have hfirst (i : iota) {y : M} (hy : y ∈ U) :
      scalarDirectional (F i) (fun z => ∑ j ∈ s, f j z) y =
        ∑ j ∈ s, scalarDirectional (F i) (f j) y :=
    scalarDirectional_finsetSum s (F i) f (fun j hj =>
      ((hf j hj).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have hsecond (i : iota) :
      scalarDirectional (F i) (scalarDirectional (F i) (fun y => ∑ j ∈ s, f j y)) x =
        ∑ j ∈ s, scalarDirectional (F i) (scalarDirectional (F i) (f j)) x := by
    have heq : scalarDirectional (F i) (fun y => ∑ j ∈ s, f j y) =ᶠ[𝓝 x]
        (fun y => ∑ j ∈ s, scalarDirectional (F i) (f j) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfirst i hy
    calc
      _ = scalarDirectional (F i) (fun y => ∑ j ∈ s, scalarDirectional (F i) (f j) y) x :=
        congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F i x)) heq.mfderiv_eq
      _ = _ := scalarDirectional_finsetSum s (F i) _ (fun j hj =>
        ((contMDiffOn_scalarDirectional hU (hf j hj) (F i)).contMDiffAt
          (hU.mem_nhds hx)).mdifferentiableAt (by simp))
  have hterm (i : iota) :
      d.fieldAdjoint (F i) (scalarDirectional (F i) (fun y => ∑ j ∈ s, f j y)) x =
        ∑ j ∈ s, d.fieldAdjoint (F i) (scalarDirectional (F i) (f j)) x := by
    simp only [FiniteChartData.fieldAdjoint, hsecond, hfirst i hx,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [scalarLaplacian, hterm]
  exact Finset.sum_comm



theorem scalarLaplacian_reconstruction {jota : Type*} (s : Finset jota)
    {U : Set M} (hU : IsOpen U) (c q : jota → M → ℝ)
    (hc : ∀ j ∈ s, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (c j) U)
    (hq : ∀ j ∈ s, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q j) U)
    {x : M} (hx : x ∈ U) :
    (∑ j ∈ s, c j x * scalarLaplacian F d (q j) x) =
      scalarLaplacian F d (fun y => ∑ j ∈ s, c j y * q j y) x -
        (∑ j ∈ s, q j x * scalarLaplacian F d (c j) x) +
        2 * ∑ j ∈ s, ∑ i,
          scalarDirectional (F i) (c j) x * scalarDirectional (F i) (q j) x := by
  have heq :
      scalarLaplacian F d (fun y => ∑ j ∈ s, c j y * q j y) x =
        ∑ j ∈ s, (c j x * scalarLaplacian F d (q j) x +
          q j x * scalarLaplacian F d (c j) x -
            2 * ∑ i, scalarDirectional (F i) (c j) x * scalarDirectional (F i) (q j) x) := by
    rw [scalarLaplacian_finsetSum F d s hU (fun j y => c j y * q j y)
      (fun j hj => (hc j hj).mul (hq j hj)) hx]
    exact Finset.sum_congr rfl (fun j hj => scalarLaplacian_mul F d hU (hc j hj) (hq j hj) hx)
  rw [heq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem contMDiffOn_pairing_fields (h : SmoothTensor (n := n) (M := M))
    (V W : (x : M) → TangentSpace (𝓡 n) x) {U : Set M}
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 n) M)) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓡 n) M)) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => h x (V x) (W x)) U := by
  have hpair := h.contMDiff.contMDiffOn.clm_bundle_apply₂ hV hW
  intro x hx
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair x hx)).2


def coframeComponent (g : RiemannianMetric n M)
    (V W : (x : M) → TangentSpace (𝓡 n) x) (ab : iota × iota) (x : M) : ℝ :=
  g.inner x (F ab.1 x) (V x) * g.inner x (F ab.2 x) (W x)


theorem smoothTensorLaplacian_component (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M))
    (V W : (x : M) → TangentSpace (𝓡 n) x) {U : Set M} (hU : IsOpen U)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 n) M)) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓡 n) M)) U)
    {x : M} (hx : x ∈ U) :
    smoothTensorLaplacian F d g h x (V x) (W x) =
      scalarLaplacian F d (fun y => h y (V y) (W y)) x -
        (∑ ab : iota × iota, scalarProbe F h ab x *
          scalarLaplacian F d (coframeComponent F g V W ab) x) +
        2 * ∑ ab : iota × iota, ∑ i,
          scalarDirectional (F i) (coframeComponent F g V W ab) x *
            scalarDirectional (F i) (scalarProbe F h ab) x := by
  have hc (ab : iota × iota) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (coframeComponent F g V W ab) U :=
    contMDiffOn_pairing_fields (coframeTensor g (F ab.1) (F ab.2)) V W hV hW
  have hq (ab : iota × iota) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (scalarProbe F h ab) U :=
    (scalarProbe_contMDiff F h ab).contMDiffOn
  have hreconstruction :
      (fun y => ∑ ab : iota × iota, coframeComponent F g V W ab y * scalarProbe F h ab y) =
        (fun y => h y (V y) (W y)) := by
    funext y
    have hid := congrArg (fun L => L (V y) (W y)) (nativeDecode_probes g F hF h y)
    rw [nativeDecode_apply] at hid
    convert hid using 1
    apply Finset.sum_congr rfl
    intro ab _
    change (g.inner y (F ab.1 y) (V y) * g.inner y (F ab.2 y) (W y)) *
      h y (F ab.1 y) (F ab.2 y) =
        h y (F ab.1 y) (F ab.2 y) * g.inner y (F ab.1 y) (V y) *
          g.inner y (F ab.2 y) (W y)
    ring
  have hidentity := scalarLaplacian_reconstruction F d Finset.univ hU
    (coframeComponent F g V W) (scalarProbe F h) (fun ab _ => hc ab) (fun ab _ => hq ab) hx
  rw [hreconstruction] at hidentity
  calc
    _ = ∑ ab : iota × iota, coframeComponent F g V W ab x *
        scalarLaplacian F d (scalarProbe F h ab) x := by
      change nativeDecode g F x (rawLaplacianCoefficients F d h x) (V x) (W x) = _
      rw [nativeDecode_apply]
      apply Finset.sum_congr rfl
      intro ab _
      change scalarLaplacian F d (scalarProbe F h ab) x * g.inner x (F ab.1 x) (V x) *
        g.inner x (F ab.2 x) (W x) =
          (g.inner x (F ab.1 x) (V x) * g.inner x (F ab.2 x) (W x)) *
            scalarLaplacian F d (scalarProbe F h ab) x
      ring
    _ = _ := hidentity


theorem projectionKernel_contMDiff (g : RiemannianMetric n M) (ab cd : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => projectionKernel g F x ab cd) :=
  (contMDiff_pairing (metricTensor g) (F cd.1) (F ab.1)).mul
    (contMDiff_pairing (metricTensor g) (F cd.2) (F ab.2))


def projectionLowerSource (g : RiemannianMetric n M) (x : M)
    (q : Coefficients iota) (dq : DerivativeCoefficients iota) (ab : iota × iota) : ℝ :=
  (∑ cd : iota × iota, q cd * scalarLaplacian F d
    (fun y => projectionKernel g F y ab cd) x) -
  2 * ∑ cd : iota × iota, ∑ i,
    scalarDirectional (F i) (fun y => projectionKernel g F y ab cd) x * dq (i, cd)



theorem scalarLaplacian_probe_eq (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M)) (ab : iota × iota) (x : M) :
    scalarLaplacian F d (scalarProbe F h ab) x =
      probes F (smoothTensorLaplacian F d g h) x ab +
        projectionLowerSource F d g x (probes F h x) (derivativeProbes F h x) ab := by
  have hcomponent := smoothTensorLaplacian_component F d g hF h
    (F ab.1) (F ab.2) isOpen_univ (F ab.1).contMDiff.contMDiffOn
      (F ab.2).contMDiff.contMDiffOn (Set.mem_univ x)
  change probes F (smoothTensorLaplacian F d g h) x ab =
    scalarLaplacian F d (scalarProbe F h ab) x -
      (∑ cd : iota × iota, (probes F h x) cd * scalarLaplacian F d
        (fun y => projectionKernel g F y ab cd) x) +
      2 * ∑ cd : iota × iota, ∑ i,
        scalarDirectional (F i) (fun y => projectionKernel g F y ab cd) x *
          (derivativeProbes F h x) (i, cd) at hcomponent
  unfold projectionLowerSource
  linarith only [hcomponent]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

private theorem directional_eq_chart_fderiv (p : M)
    (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (chartAt ModelE p).source)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    scalarDirectional V f ((chartAt ModelE p).symm z) =
      fderiv ℝ (f ∘ (chartAt ModelE p).symm) z (chartField p V z) := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  have he : e.MDifferentiable (𝓡 n) 𝓘(ℝ, ModelE) := mdifferentiable_chart (I := 𝓡 n) p
  have hinv := he.symm_comp_deriv (e.map_target hz)
  rw [e.right_inv hz] at hinv
  have hvinv : mfderiv 𝓘(ℝ, ModelE) (𝓡 n) e.symm z (chartField p V z) =
      V (e.symm z) := by
    exact congrArg (fun L : TangentSpace (𝓡 n) (e.symm z) →L[ℝ]
      TangentSpace (𝓡 n) (e.symm z) => L (V (e.symm z))) hinv
  have hfd := (hf.contMDiffAt (e.open_source.mem_nhds (e.map_target hz))).mdifferentiableAt
    (by simp)
  have hchain := mfderiv_comp_apply z hfd (he.mdifferentiableAt_symm hz) (chartField p V z)
  rw [mfderiv_eq_fderiv] at hchain
  exact (hchain.trans (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)) hvinv)).symm

private theorem directional_twice_eq_chart_hessian (p : M)
    (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (chartAt ModelE p).source)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    scalarDirectional V (scalarDirectional V f) ((chartAt ModelE p).symm z) =
      fderiv ℝ (fderiv ℝ (f ∘ (chartAt ModelE p).symm)) z
        (chartField p V z) (chartField p V z) +
      fderiv ℝ (f ∘ (chartAt ModelE p).symm) z
        (fderiv ℝ (chartField p V) z (chartField p V z)) := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  have hfchart : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
    (hf.comp (contMDiffOn_chart_symm (I := 𝓡 n) (x := p)) e.symm.mapsTo).contDiffOn
  have hH := ((hfchart.fderiv_of_isOpen (m := ∞) e.open_target (by simp)).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hV := ((contDiffOn_chartField p V).contDiffAt
    (e.open_target.mem_nhds hz)).differentiableAt (by simp)
  have heq : (scalarDirectional V f ∘ e.symm) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (f ∘ e.symm) y (chartField p V y)) := by
    filter_upwards [e.open_target.mem_nhds hz] with y hy
    exact directional_eq_chart_fderiv p V hf hy
  rw [directional_eq_chart_fderiv p V
    (contMDiffOn_scalarDirectional e.open_source hf V) hz, heq.fderiv_eq,
    fderiv_clm_apply hH hV]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _


theorem chartField_bilinear_trace (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {z : ModelE} (hz : z ∈ (chartAt ModelE p).target)
    (B : ModelE →L[ℝ] ModelE →L[ℝ] ℝ) :
    (∑ a, B (chartField p (F a) z) (chartField p (F a) z)) =
      ∑ i : Fin n, ∑ j : Fin n,
        (DeTurckNative.chartMetricCoefficients g p z)⁻¹ i j *
          B ((PiLp.basisFun 2 ℝ (Fin n)) i) ((PiLp.basisFun 2 ℝ (Fin n)) j) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  let x : M := e.symm z
  have hx : x ∈ e.source := e.map_target hz
  let J := DeTurckNative.chartDifferentialEquiv p x hx
  let b := DeTurckNative.chartFrameBasis p x hx
  have hJ : (J : TangentSpace (𝓡 n) x →L[ℝ] ModelE) =
      mfderiv (𝓡 n) 𝓘(ℝ, ModelE) e x :=
    (DeTurckNative.chartDifferentialEquiv_coe p x hx).trans
      (hasMFDerivAt_extChartAt (I := 𝓡 n) hx).mfderiv
  have hJF (a : iota) : J (F a x) = chartField p (F a) z :=
    congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ModelE => L (F a x)) hJ
  have hJb (a : Fin n) : J (b a) = (PiLp.basisFun 2 ℝ (Fin n)) a := by
    change J (J.symm ((PiLp.basisFun 2 ℝ (Fin n)) a)) = _
    exact J.apply_symm_apply _
  have hgram : Matrix.gram ℝ b = DeTurckNative.chartMetricCoefficients g p z := by
    have hback : (extChartAt (𝓡 n) p).symm z = x := rfl
    ext a c
    change g.inner x (b a) (b c) =
      g.inner ((extChartAt (𝓡 n) p).symm z)
        (DeTurckNative.chartFrame p a ((extChartAt (𝓡 n) p).symm z))
        (DeTurckNative.chartFrame p c ((extChartAt (𝓡 n) p).symm z))
    rw [hback, DeTurckNative.chartFrame_eq_basis p x hx a,
      DeTurckNative.chartFrame_eq_basis p x hx c]
  have htrace := ParsevalFrameNative.parseval_trace_eq_inverse_gram
    (fun a => F a x) (hF x) (g.orthonormalBasis x) b
    (B.bilinearComp (J : TangentSpace (𝓡 n) x →L[ℝ] ModelE)
      (J : TangentSpace (𝓡 n) x →L[ℝ] ModelE))
  change (∑ a, B (J (F a x)) (J (F a x))) =
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * B (J (b i)) (J (b j)) at htrace
  simpa only [hJF, hJb, hgram] using htrace


def scalarChartLowerTerm (p : M) (f : M → ℝ) (z : ModelE) : ℝ :=
  ∑ a,
    (fderiv ℝ (f ∘ (chartAt ModelE p).symm) z
      (fderiv ℝ (chartField p (F a)) z (chartField p (F a) z)) +
    d.fieldDivergence (F a) ((chartAt ModelE p).symm z) *
      fderiv ℝ (f ∘ (chartAt ModelE p).symm) z (chartField p (F a) z))


theorem scalarLaplacian_chart_principal (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (p : M) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (chartAt ModelE p).source)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    scalarLaplacian F d f ((chartAt ModelE p).symm z) =
      -(∑ i : Fin n, ∑ j : Fin n,
        (DeTurckNative.chartMetricCoefficients g p z)⁻¹ i j *
          fderiv ℝ (fderiv ℝ (f ∘ (chartAt ModelE p).symm)) z
            ((PiLp.basisFun 2 ℝ (Fin n)) i) ((PiLp.basisFun 2 ℝ (Fin n)) j)) -
        scalarChartLowerTerm F d p f z := by
  classical
  rw [← chartField_bilinear_trace F g hF p hz]
  unfold scalarLaplacian scalarChartLowerTerm
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  unfold FiniteChartData.fieldAdjoint
  rw [directional_twice_eq_chart_hessian p (F a) hf hz,
    directional_eq_chart_fderiv p (F a) hf hz]
  ring


def tensorChartLowerTerm (g : RiemannianMetric n M)
    (h : SmoothTensor (n := n) (M := M)) (p : M) (i j : Fin n) (z : ModelE) : ℝ :=
  let V := DeTurckNative.chartFrame p i
  let W := DeTurckNative.chartFrame p j
  let x := (chartAt ModelE p).symm z;
  -scalarChartLowerTerm F d p (fun y => h y (V y) (W y)) z -
    (∑ ab : iota × iota, scalarProbe F h ab x *
      scalarLaplacian F d (coframeComponent F g V W ab) x) +
    2 * (∑ ab : iota × iota, ∑ a,
      scalarDirectional (F a) (coframeComponent F g V W ab) x *
        scalarDirectional (F a) (scalarProbe F h ab) x)


theorem smoothTensorLaplacian_chart_principal (g : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M)) (p : M) (i j : Fin n)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    smoothTensorLaplacian F d g h ((chartAt ModelE p).symm z)
        (DeTurckNative.chartFrame p i ((chartAt ModelE p).symm z))
        (DeTurckNative.chartFrame p j ((chartAt ModelE p).symm z)) =
      -(∑ a : Fin n, ∑ b : Fin n,
        (DeTurckNative.chartMetricCoefficients g p z)⁻¹ a b *
          fderiv ℝ (fderiv ℝ ((fun y => h y (DeTurckNative.chartFrame p i y)
            (DeTurckNative.chartFrame p j y)) ∘ (chartAt ModelE p).symm)) z
            ((PiLp.basisFun 2 ℝ (Fin n)) a) ((PiLp.basisFun 2 ℝ (Fin n)) b)) +
      tensorChartLowerTerm F d g h p i j z := by
  have hV := DeTurckNative.chartFrame_contMDiffOn p i
  have hW := DeTurckNative.chartFrame_contMDiffOn p j
  rw [smoothTensorLaplacian_component F d g hF h _ _ (chartAt ModelE p).open_source
    hV hW ((chartAt ModelE p).map_target hz)]
  rw [scalarLaplacian_chart_principal F d g hF p
    (contMDiffOn_pairing_fields h _ _ hV hW) hz]
  dsimp only [tensorChartLowerTerm]
  ring

private theorem secondFDeriv_sub_on {f q : ModelE → ℝ} {U : Set ModelE}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hq : ContDiffOn ℝ ∞ q U)
    {z : ModelE} (hz : z ∈ U) :
    fderiv ℝ (fderiv ℝ (fun y => f y - q y)) z =
      fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ q) z := by
  have heq : fderiv ℝ (fun y => f y - q y) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ f y - fderiv ℝ q y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact fderiv_fun_sub ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hq.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [heq.fderiv_eq]
  exact fderiv_fun_sub
    (((hf.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
    (((hq.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

private theorem chartMetricJet_second_eq_hessian (g : RiemannianMetric n M)
    (p : M) {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) (a b i j : Fin n) :
    (DeTurckNative.coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (DeTurckNative.chartMetricCoefficients g p) z).second a b i j =
      fderiv ℝ (fderiv ℝ (fun y => DeTurckNative.chartMetricCoefficients g p y i j)) z
        ((PiLp.basisFun 2 ℝ (Fin n)) a) ((PiLp.basisFun 2 ℝ (Fin n)) b) := by
  have hG : ContDiffOn ℝ ∞ (fun y => DeTurckNative.chartMetricCoefficients g p y i j)
      (chartAt ModelE p).target := by
    simpa using DeTurckNative.chartMetricCoefficients_contDiffOn g p i j
  have hD := ((hG.fderiv_of_isOpen (m := ∞) (chartAt ModelE p).open_target (by simp)).contDiffAt
    ((chartAt ModelE p).open_target.mem_nhds hz)).differentiableAt (by simp)
  change fderiv ℝ (fun y => fderiv ℝ
    (fun w => DeTurckNative.chartMetricCoefficients g p w i j) y
      ((PiLp.basisFun 2 ℝ (Fin n)) b)) z ((PiLp.basisFun 2 ℝ (Fin n)) a) = _
  rw [fderiv_clm_apply hD (by fun_prop)]
  simp


def smoothCoreResidual {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) (x : M)
    (v w : TangentSpace (𝓡 n) x) : ℝ :=
  smoothTensorLaplacian F d g0 h x v w - 2 * D.ricci x v w +
    DeTurckNative.metricLieDerivative D (DeTurckNative.intrinsicDeTurckField D B) x v w


def smoothResidualTensor {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) : SmoothTensor (n := n) (M := M) :=
  smoothTensorLaplacian F d g0 h + DeTurckNative.smoothRicciDeTurckTensor D B

@[simp] theorem smoothResidualTensor_apply {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    smoothResidualTensor F d D B h x v w = smoothCoreResidual F d D B h x v w := by
  change smoothTensorLaplacian F d g0 h x v w +
    DeTurckNative.smoothRicciDeTurckTensor D B x v w = _
  rw [DeTurckNative.smoothRicciDeTurckTensor_apply]
  unfold smoothCoreResidual
  ring

theorem smoothResidualTensor_symm {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    smoothResidualTensor F d D B h x v w = smoothResidualTensor F d D B h x w v := by
  change smoothTensorLaplacian F d g0 h x v w + DeTurckNative.smoothRicciDeTurckTensor D B x v w =
    smoothTensorLaplacian F d g0 h x w v + DeTurckNative.smoothRicciDeTurckTensor D B x w v
  rw [smoothTensorLaplacian_symm F d g0 h hsymm x v w,
    DeTurckNative.smoothRicciDeTurckTensor_symm D B x v w]

theorem smoothCoreResidual_symm {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M))
    (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    smoothCoreResidual F d D B h x v w = smoothCoreResidual F d D B h x w v := by
  simpa only [smoothResidualTensor_apply] using smoothResidualTensor_symm F d D B h hsymm x v w



theorem smoothCoreResidual_eq_perturbationRemainder
    {g0 g : RiemannianMetric n M} (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x), (∑ i, g0.inner x (F i x) v • F i x) = v)
    (h : SmoothTensor (n := n) (M := M))
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g0.inner x v w + h x v w)
    (p : M) (i j : Fin n) {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    let bg := DeTurckNative.coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (DeTurckNative.chartMetricCoefficients g0 p) z
    let q := DeTurckNative.coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
      (DeTurckNative.chartMetricCoefficients g p) z
    smoothCoreResidual F d D B h ((chartAt ModelE p).symm z)
        (DeTurckNative.chartFrame p i ((chartAt ModelE p).symm z))
        (DeTurckNative.chartFrame p j ((chartAt ModelE p).symm z)) =
      DeTurckNative.perturbationRemainder bg
        (DeTurckNative.backgroundLowerJet q - DeTurckNative.backgroundLowerJet bg)
        (q.second - bg.second) i j + tensorChartLowerTerm F d g0 h p i j z := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  let bg := DeTurckNative.coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
    (DeTurckNative.chartMetricCoefficients g0 p) z
  let q := DeTurckNative.coordinateMetricJet (PiLp.basisFun 2 ℝ (Fin n))
    (DeTurckNative.chartMetricCoefficients g p) z
  let H : ModelE → ℝ := (fun y => h y (DeTurckNative.chartFrame p i y)
    (DeTurckNative.chartFrame p j y)) ∘ e.symm
  have hH : H = (fun y => DeTurckNative.chartMetricCoefficients g p y i j -
      DeTurckNative.chartMetricCoefficients g0 p y i j) := by
    funext y
    have hsum := hmetric (e.symm y) (DeTurckNative.chartFrame p i (e.symm y))
      (DeTurckNative.chartFrame p j (e.symm y))
    change h (e.symm y) (DeTurckNative.chartFrame p i (e.symm y))
      (DeTurckNative.chartFrame p j (e.symm y)) = _
    change h (e.symm y) (DeTurckNative.chartFrame p i (e.symm y))
      (DeTurckNative.chartFrame p j (e.symm y)) =
      g.inner (e.symm y) (DeTurckNative.chartFrame p i (e.symm y))
        (DeTurckNative.chartFrame p j (e.symm y)) -
      g0.inner (e.symm y) (DeTurckNative.chartFrame p i (e.symm y))
        (DeTurckNative.chartFrame p j (e.symm y))
    linarith only [hsum]
  have hG : ContDiffOn ℝ ∞ (fun y => DeTurckNative.chartMetricCoefficients g p y i j)
      e.target := by simpa using DeTurckNative.chartMetricCoefficients_contDiffOn g p i j
  have hG0 : ContDiffOn ℝ ∞ (fun y => DeTurckNative.chartMetricCoefficients g0 p y i j)
      e.target := by simpa using DeTurckNative.chartMetricCoefficients_contDiffOn g0 p i j
  have hsecond (a b : Fin n) :
      (q.second - bg.second) a b i j = fderiv ℝ (fderiv ℝ H) z
        ((PiLp.basisFun 2 ℝ (Fin n)) a) ((PiLp.basisFun 2 ℝ (Fin n)) b) := by
    simp only [Pi.sub_apply, Matrix.sub_apply]
    rw [chartMetricJet_second_eq_hessian g p hz,
      chartMetricJet_second_eq_hessian g0 p hz, hH,
      secondFDeriv_sub_on e.open_target hG hG0 hz]
    rfl
  have hcontract :
      DeTurckNative.lowerJetContraction bg.value⁻¹ (q.second - bg.second) i j =
        ∑ a : Fin n, ∑ b : Fin n,
          (DeTurckNative.chartMetricCoefficients g0 p z)⁻¹ a b *
            fderiv ℝ (fderiv ℝ H) z ((PiLp.basisFun 2 ℝ (Fin n)) a)
              ((PiLp.basisFun 2 ℝ (Fin n)) b) := by
    change (∑ a : Fin n, ∑ b : Fin n,
      (DeTurckNative.chartMetricCoefficients g0 p z)⁻¹ a b *
        (q.second - bg.second) a b i j) = _
    simp only [hsecond]
  have hsource := DeTurckNative.ricciDeTurckSource_coordinateMetricJet_eq_intrinsic
    D B p (e.map_target hz) i j
  have hchart : extChartAt (𝓡 n) p (e.symm z) = z := e.right_inv hz
  rw [hchart] at hsource
  have hrem : DeTurckNative.perturbationRemainder bg
      (DeTurckNative.backgroundLowerJet q - DeTurckNative.backgroundLowerJet bg)
      (q.second - bg.second) i j =
        DeTurckNative.ricciDeTurckSource bg q i j -
          DeTurckNative.lowerJetContraction bg.value⁻¹ (q.second - bg.second) i j := by
    simp only [DeTurckNative.perturbationRemainder, add_sub_cancel]
    rfl
  change smoothCoreResidual F d D B h (e.symm z)
      (DeTurckNative.chartFrame p i (e.symm z)) (DeTurckNative.chartFrame p j (e.symm z)) = _
  rw [hrem, hcontract, hsource]
  unfold smoothCoreResidual
  rw [smoothTensorLaplacian_chart_principal F d g0 hF h p i j hz]
  dsimp only [H]
  ring

end LocalProduct


def coreResidualL2 {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) : tensorL2 F d.measure :=
  intoTensorL2 F d.measure (smoothResidualTensor F d D B h)

theorem coreResidualL2_coe {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) :
    (coreResidualL2 F d D B h : Lp (Coefficients iota) 2 d.measure) =ᵐ[d.measure]
      fun x => WithLp.toLp 2 (fun ab : iota × iota =>
        smoothCoreResidual F d D B h x (F ab.1 x) (F ab.2 x)) := by
  have heq := tensorToLp_coe F d.measure (smoothResidualTensor F d D B h)
  filter_upwards [heq] with x hx
  rw [show (coreResidualL2 F d D B h : Lp (Coefficients iota) 2 d.measure) =
    tensorToLp F d.measure (smoothResidualTensor F d D B h) from rfl, hx]
  apply PiLp.ext
  rintro ⟨a, b⟩
  exact smoothResidualTensor_apply F d D B h x (F a x) (F b x)

theorem coreResidualL2_norm_sq {g0 g : RiemannianMetric n M}
    (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (h : SmoothTensor (n := n) (M := M)) :
    ‖coreResidualL2 F d D B h‖ ^ 2 =
      ∫ x, ‖WithLp.toLp 2 (fun ab : iota × iota =>
        smoothCoreResidual F d D B h x (F ab.1 x) (F ab.2 x))‖ ^ 2 ∂d.measure := by
  change ‖tensorToLp F d.measure (smoothResidualTensor F d D B h)‖ ^ 2 = _
  rw [tensorToLp_norm_sq]
  apply integral_congr_ae
  filter_upwards with x
  have heq : probes F (smoothResidualTensor F d D B h) x =
      WithLp.toLp 2 (fun ab : iota × iota =>
        smoothCoreResidual F d D B h x (F ab.1 x) (F ab.2 x)) := by
    apply PiLp.ext
    rintro ⟨a, b⟩
    exact smoothResidualTensor_apply F d D B h x (F a x) (F b x)
  rw [heq]

end PoincareConjecture.TensorProbeNative
