import PoincareConjecture.Proofs.M03.Existence.TensorHilbertNative









set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv

universe u

namespace PoincareConjecture.NativeLocalizedEllipticEquationNative

open TensorProbeNative ChartMeasureNative TensorHilbertNative
  NativeChartScalarLocalization EuclideanDerivativeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric n M} (d : TensorHilbertNative.Data g)
  (L : FiniteChartLocalizationData d.charts) (a : L.patches)

local notation "E" => EuclideanSpace ℝ (Fin n)


def densityTest (φ : 𝓢(E, ℝ)) (x : M) : ℝ :=
  L.weight a x * (φ (L.chart a x) / d.charts.chartDensity a.val.1.val (L.chart a x))

theorem densityTest_contMDiff (φ : 𝓢(E, ℝ)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (densityTest d L a φ) := by
  have h := FiniteChartData.contMDiff_weight_mul_chart a.val.1.val
    (L.weight_smooth a) (L.weight_support_source a)
    (b := fun z => φ z / d.charts.chartDensity a.val.1.val z)
    ((φ.smooth ⊤).contDiffOn.div (d.charts.chartDensity_contDiffOn a.val.1.val)
      (fun x hx => (d.charts.chartDensity_pos a.val.1.val hx).ne'))
  change ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
    (fun x => L.weight a x * (φ (chartAt E a.val.1.val x) /
      d.charts.chartDensity a.val.1.val (chartAt E a.val.1.val x)))
  exact h

theorem densityTest_zero_off_weight (φ : 𝓢(E, ℝ)) {x : M}
    (hx : x ∉ tsupport (L.weight a)) : densityTest d L a φ x = 0 := by
  rw [densityTest, image_eq_zero_of_notMem_tsupport hx, zero_mul]


theorem densityTest_pairing_smooth (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ))
    (h : SmoothTensor (n := n) (M := M)) :
    inner ℝ (d.scalarLp (densityTest d L a φ) (densityTest_contMDiff d L a φ))
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) =
    inner ℝ (L.localizationL2 a
      (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h))) (φ.toLp 2 volume) := by
  let p : M := a.val.1.val
  let e : OpenPartialHomeomorph M E := chartAt E p
  have hprod : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => densityTest d L a φ x * scalarProbe d.fields h ab x) :=
    (densityTest_contMDiff d L a φ).mul (scalarProbe_contMDiff d.fields h ab)
  have hzero : ∀ x ∉ tsupport (L.weight a),
      densityTest d L a φ x * scalarProbe d.fields h ab x = 0 := by
    intro x hx
    rw [densityTest_zero_off_weight d L a φ hx, zero_mul]
  have hloc := d.localizedValue_into L a ab h
  change L.localizationL2 a
    (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h)) =
      (d.localizedSchwartz L a ab h).toLp 2 volume at hloc
  rw [hloc, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, densityTest d L a φ x * scalarProbe d.fields h ab x ∂d.charts.measure := by
      apply integral_congr_ae
      filter_upwards [d.scalarLp_coe (densityTest d L a φ) (densityTest_contMDiff d L a φ),
        d.valueCoefficient_into_coe ab h] with x htest hq
      rw [htest, hq, Real.inner_apply]
    _ = ∫ z, d.charts.chartDensity p z *
        chartScalar p (fun x => densityTest d L a φ x * scalarProbe d.fields h ab x) z :=
      d.charts.integral_eq_chartDensity p hprod (L.weight_compactSupport a)
        (L.weight_support_source a) hzero
    _ = ∫ z, d.localizedSchwartz L a ab h z * φ z := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      dsimp only
      rw [d.localizedSchwartz_apply]
      by_cases hz : z ∈ e.target
      · rw [chartScalar_of_mem p _ hz, chartScalar_of_mem p _ hz]
        change d.charts.chartDensity p z *
          ((L.weight a (e.symm z) * (φ (e (e.symm z)) /
            d.charts.chartDensity p (e (e.symm z)))) * scalarProbe d.fields h ab (e.symm z)) = _
        rw [e.right_inv hz]
        field_simp [(d.charts.chartDensity_pos p hz).ne']
        dsimp only [e]
        ring
      · rw [chartScalar_of_notMem p _ hz, chartScalar_of_notMem p _ hz, mul_zero, zero_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(d.localizedSchwartz L a ab h).coeFn_toLp 2 volume,
        φ.coeFn_toLp 2 volume] with x hr hphi
      rw [hr, hphi, Real.inner_apply]


theorem densityTest_pairing (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (v : d.Value) :
    inner ℝ (d.scalarLp (densityTest d L a φ) (densityTest_contMDiff d L a φ))
      (d.valueCoefficient ab v) =
    inner ℝ (L.localizationL2 a (d.valueCoefficient ab v)) (φ.toLp 2 volume) := by
  have heq :
      (fun v : d.Value =>
        inner ℝ (d.scalarLp (densityTest d L a φ) (densityTest_contMDiff d L a φ))
          (d.valueCoefficient ab v)) =
      (fun v : d.Value =>
        inner ℝ (L.localizationL2 a (d.valueCoefficient ab v)) (φ.toLp 2 volume)) := by
    apply (intoTensorL2_denseRange d.fields d.charts.measure).equalizer
      (continuous_const.inner (d.valueCoefficient ab).continuous)
      (((L.localizationL2 a).continuous.comp (d.valueCoefficient ab).continuous).inner continuous_const)
    funext h
    exact densityTest_pairing_smooth d L a ab φ h
  exact congrFun heq v

def densityTensorTest (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) :
    SmoothTensor (n := n) (M := M) :=
  d.scalarTest ab (densityTest d L a φ) (densityTest_contMDiff d L a φ)

theorem densityTensorTest_pairing (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (v : d.Value) :
    inner ℝ (intoTensorL2 d.fields d.charts.measure (densityTensorTest d L a ab φ)) v =
      inner ℝ (L.localizationL2 a (d.valueCoefficient ab v)) (φ.toLp 2 volume) := by
  rw [densityTensorTest, d.scalarTest_pairing, densityTest_pairing]

def principalCoefficient (g : RiemannianMetric n M) (p : M) (i j : Fin n) (z : E) : ℝ :=
  (DeTurckNative.chartMetricCoefficients g p z)⁻¹ i j

theorem principalCoefficient_contDiffOn (g : RiemannianMetric n M) (p : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (principalCoefficient g p i j) (chartAt E p).target := by
  have hG : ContDiffOn ℝ ∞
      (fun z i j => DeTurckNative.chartMetricCoefficients g p z i j) (chartAt E p).target := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    simpa using DeTurckNative.chartMetricCoefficients_contDiffOn g p i j
  intro z hz
  have hpos : (DeTurckNative.chartMetricCoefficients g p z).PosDef :=
    DeTurckNative.chartMetricCoefficients_posDef g p (by simpa using hz)
  have hdet := ((DeTurckNative.chartMetricCoefficients g p z).isUnit_iff_isUnit_det.mp
    hpos.isUnit).ne_zero
  have hinv := (DeTurckNative.contDiffAt_matrixInverseEntries_infty
    (fun i j => DeTurckNative.chartMetricCoefficients g p z i j) hdet).comp z
      (hG.contDiffAt ((chartAt E p).open_target.mem_nhds hz))
  have hentry := ((contDiffAt_pi.mp (contDiffAt_pi.mp hinv i)) j).contDiffWithinAt
    (s := (chartAt E p).target)
  change ContDiffWithinAt ℝ ∞ (principalCoefficient g p i j) (chartAt E p).target z at hentry
  exact hentry


def driftCoefficient (p : M) (j : Fin n) (z : E) : ℝ :=
  ∑ r : Fin d.fieldCount,
    ((fderiv ℝ (chartField p (d.fields r)) z (chartField p (d.fields r) z)) j +
      d.charts.fieldDivergence (d.fields r) ((chartAt E p).symm z) * chartField p (d.fields r) z j)

theorem driftCoefficient_contDiffOn (p : M) (j : Fin n) :
    ContDiffOn ℝ ∞ (driftCoefficient d p j) (chartAt E p).target := by
  apply ContDiffOn.sum
  intro r _
  have hV := contDiffOn_chartField p (d.fields r)
  have hDV := (hV.fderiv_of_isOpen (m := ∞) (chartAt E p).open_target (by simp)).clm_apply hV
  exact ((contDiffOn_piLp 2).mp hDV j).add
    ((contDiffOn_scalar_chartInverse p (d.charts.fieldDivergence_contMDiff (d.fields r))).mul
      (contDiffOn_chartField_coordinate p (d.fields r) j))

private theorem clm_basis_expansion (A : E →L[ℝ] ℝ) (v : E) :
    A v = ∑ j : Fin n, v j * A ((PiLp.basisFun 2 ℝ (Fin n)) j) := by
  have hv : (∑ j : Fin n, v j • (PiLp.basisFun 2 ℝ (Fin n)) j) = v := by
    simpa only [PiLp.basisFun_repr] using (PiLp.basisFun 2 ℝ (Fin n)).sum_repr v
  have h := congrArg A hv
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

theorem scalarChartLowerTerm_eq (p : M) (f : M → ℝ) (z : E) :
    scalarChartLowerTerm d.fields d.charts p f z =
      ∑ j : Fin n, driftCoefficient d p j z *
        fderiv ℝ (f ∘ (chartAt E p).symm) z ((PiLp.basisFun 2 ℝ (Fin n)) j) := by
  let A : E →L[ℝ] ℝ := fderiv ℝ (f ∘ (chartAt E p).symm) z
  let V (r : Fin d.fieldCount) : E := chartField p (d.fields r) z
  let Q (r : Fin d.fieldCount) : E := fderiv ℝ (chartField p (d.fields r)) z (V r)
  let B (r : Fin d.fieldCount) : ℝ :=
    d.charts.fieldDivergence (d.fields r) ((chartAt E p).symm z)
  change (∑ r : Fin d.fieldCount, (A (Q r) + B r * A (V r))) =
    ∑ j : Fin n, (∑ r : Fin d.fieldCount, ((Q r) j + B r * V r j)) *
      A ((PiLp.basisFun 2 ℝ (Fin n)) j)
  calc
    _ = ∑ r : Fin d.fieldCount, ∑ j : Fin n,
        ((Q r) j + B r * V r j) * A ((PiLp.basisFun 2 ℝ (Fin n)) j) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [clm_basis_expansion A (Q r), clm_basis_expansion A (V r),
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

theorem cutoff_compactSupport : HasCompactSupport (L.scalarCutoff a) :=
  chartScalar_compactSupport a.val.1.val (L.weight_compactSupport a)
    (L.weight_support_source a) (L.weight_zero_off_support a)

theorem cutoff_support_target :
    tsupport (L.scalarCutoff a) ⊆ (chartAt E a.val.1.val).target :=
  (L.scalarCutoff_tsupport_subset a).trans (L.region_subset_target a)


def cutoffCoefficient (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b (chartAt E a.val.1.val).target) : 𝓢(E, ℝ) :=
  cutoffSchwartz θ ((cutoff_compactSupport d L a).of_isClosed_subset (isClosed_tsupport θ) hθ)
    (chartAt E a.val.1.val).open_target (hθ.trans (cutoff_support_target d L a)) b hb

@[simp] theorem cutoffCoefficient_apply (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b (chartAt E a.val.1.val).target) (x : E) :
    cutoffCoefficient d L a θ hθ b hb x = θ x * b x := rfl

theorem cutoffCoefficient_support (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b (chartAt E a.val.1.val).target) :
    tsupport (cutoffCoefficient d L a θ hθ b hb) ⊆ tsupport (L.scalarCutoff a) :=
  tsupport_mul_subset_left.trans hθ

def zeroOrderCutoff : 𝓢(E, ℝ) :=
  -∑ i : Fin n, ∑ j : Fin n,
    cutoffCoefficient d L a
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a)))
      ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans
        (SchwartzMap.tsupport_lineDerivOp_subset _ _))
      (principalCoefficient g a.val.1.val i j) (principalCoefficient_contDiffOn g a.val.1.val i j)

def firstOrderCutoff (r : Fin d.fieldCount) : 𝓢(E, ℝ) :=
  (∑ j : Fin n, cutoffCoefficient d L a (L.scalarCutoff a) (Subset.refl _)
    (fun z => driftCoefficient d a.val.1.val j z *
      chartParsevalCoefficient g d.fields a.val.1.val j r z)
    ((driftCoefficient_contDiffOn d a.val.1.val j).mul
      (chartParsevalCoefficient_contDiffOn g d.fields a.val.1.val j r))) -
  ∑ i : Fin n, ∑ j : Fin n,
    (cutoffCoefficient d L a (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a))
      (SchwartzMap.tsupport_lineDerivOp_subset _ _)
      (fun z => principalCoefficient g a.val.1.val i j z *
        chartParsevalCoefficient g d.fields a.val.1.val j r z)
      ((principalCoefficient_contDiffOn g a.val.1.val i j).mul
        (chartParsevalCoefficient_contDiffOn g d.fields a.val.1.val j r)) +
    cutoffCoefficient d L a (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} (L.scalarCutoff a))
      (SchwartzMap.tsupport_lineDerivOp_subset _ _)
      (fun z => principalCoefficient g a.val.1.val i j z *
        chartParsevalCoefficient g d.fields a.val.1.val i r z)
      ((principalCoefficient_contDiffOn g a.val.1.val i j).mul
        (chartParsevalCoefficient_contDiffOn g d.fields a.val.1.val i r)))

private theorem tsupport_schwartz_sum {ι : Type*} [Fintype ι]
    (f : ι → 𝓢(E, ℝ)) {K : Set E} (hK : IsClosed K)
    (hf : ∀ i, tsupport (f i) ⊆ K) : tsupport ((∑ i, f i : 𝓢(E, ℝ)) : E → ℝ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  apply hx
  simp only [sum_apply]
  exact Finset.sum_eq_zero (fun i _ => image_eq_zero_of_notMem_tsupport (fun hi => hxK (hf i hi)))

theorem zeroOrderCutoff_support :
    tsupport (zeroOrderCutoff d L a) ⊆ tsupport (L.scalarCutoff a) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxK
  apply hx
  have hz (i j : Fin n) :
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a))) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hxK
      (SchwartzMap.tsupport_lineDerivOp_subset _ _
        (SchwartzMap.tsupport_lineDerivOp_subset _ _ ht)))
  simp only [zeroOrderCutoff, neg_apply, sum_apply, cutoffCoefficient_apply,
    hz, zero_mul, Finset.sum_const_zero, neg_zero]

theorem firstOrderCutoff_support (r : Fin d.fieldCount) :
    tsupport (firstOrderCutoff d L a r) ⊆ tsupport (L.scalarCutoff a) := by
  unfold firstOrderCutoff
  apply (tsupport_sub _ _).trans
  apply union_subset
  · apply tsupport_schwartz_sum _ (isClosed_tsupport _)
    intro j
    exact cutoffCoefficient_support d L a _ _ _ _
  · apply tsupport_schwartz_sum _ (isClosed_tsupport _)
    intro i
    apply tsupport_schwartz_sum _ (isClosed_tsupport _)
    intro j
    exact (tsupport_add _ _).trans (union_subset
      (cutoffCoefficient_support d L a _ _ _ _) (cutoffCoefficient_support d L a _ _ _ _))

theorem zeroOrderCutoff_apply (x : E) :
    zeroOrderCutoff d L a x =
      -(∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a))) x) := by
  simp only [zeroOrderCutoff, SchwartzMap.neg_apply, SchwartzMap.sum_apply,
    cutoffCoefficient_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem firstOrderCutoff_apply (r : Fin d.fieldCount) (x : E) :
    firstOrderCutoff d L a r x =
      L.scalarCutoff a x * (∑ j : Fin n, driftCoefficient d a.val.1.val j x *
        chartParsevalCoefficient g d.fields a.val.1.val j r x) -
      ∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
        ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a)) x *
          chartParsevalCoefficient g d.fields a.val.1.val j r x +
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} (L.scalarCutoff a)) x *
          chartParsevalCoefficient g d.fields a.val.1.val i r x) := by
  simp only [firstOrderCutoff, SchwartzMap.sub_apply, SchwartzMap.sum_apply,
    SchwartzMap.add_apply, cutoffCoefficient_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem localizedSchwartz_eq_cutoffCoefficient (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    d.localizedSchwartz L a ab h =
      cutoffCoefficient d L a (L.scalarCutoff a) (Subset.refl _)
        (scalarProbe d.fields h ab ∘ (L.chart a).symm)
        (contDiffOn_scalar_chartInverse a.val.1.val (scalarProbe_contMDiff d.fields h ab)) := by
  ext x
  exact (L.scalarCutoff_mul_eq_chartScalar a (scalarProbe d.fields h ab) x).symm

theorem localizedSchwartz_support (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    tsupport (d.localizedSchwartz L a ab h) ⊆ tsupport (L.scalarCutoff a) := by
  rw [localizedSchwartz_eq_cutoffCoefficient]
  exact cutoffCoefficient_support d L a _ _ _ _

theorem cutoffCoefficient_lineDeriv_apply (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (L.chart a).target) (x v : E) :
    (∂_{v} (cutoffCoefficient d L a θ hθ f hf)) x =
      θ x * fderiv ℝ f x v + f x * (∂_{v} θ) x := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact fderiv_cutoff_mul θ (L.chart a).open_target
    (hθ.trans (cutoff_support_target d L a)) hf x v


theorem cutoffCoefficient_secondLineDeriv_apply (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f (L.chart a).target) {x : E}
    (hx : x ∈ (L.chart a).target) (v w : E) :
    (∂_{w} (∂_{v} (cutoffCoefficient d L a θ hθ f hf))) x =
      θ x * fderiv ℝ (fderiv ℝ f) x v w +
        (∂_{v} θ) x * fderiv ℝ f x w +
        (∂_{w} θ) x * fderiv ℝ f x v + f x * (∂_{w} (∂_{v} θ)) x := by
  have hfc := hf.contDiffAt ((L.chart a).open_target.mem_nhds hx)
  have hdf := ((hf.fderiv_of_isOpen (m := ∞) (L.chart a).open_target (by simp)).contDiffAt
    ((L.chart a).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hfirst : ((∂_{v} (cutoffCoefficient d L a θ hθ f hf) : 𝓢(E, ℝ)) : E → ℝ) =
      fun y => θ y * fderiv ℝ f y v + f y * (∂_{v} θ) y := by
    funext y
    exact cutoffCoefficient_lineDeriv_apply d L a θ hθ f hf y v
  have hθv : DifferentiableAt ℝ ((∂_{v} θ : 𝓢(E, ℝ)) : E → ℝ) x :=
    (∂_{v} θ : 𝓢(E, ℝ)).differentiableAt
  have hleft : DifferentiableAt ℝ (fun y => θ y * fderiv ℝ f y v) x :=
    θ.differentiableAt.mul (hdf.clm_apply (differentiableAt_const v))
  have hright : DifferentiableAt ℝ (fun y => f y * (∂_{v} θ) y) x :=
    (hfc.differentiableAt (by simp)).mul hθv
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfirst,
    fderiv_fun_add hleft hright,
    ContinuousLinearMap.add_apply,
    fderiv_fun_mul (c := (θ : E → ℝ)) (d := fun y => fderiv ℝ f y v)
      θ.differentiableAt (hdf.clm_apply (differentiableAt_const v)),
    fderiv_fun_mul (c := f) (d := ((∂_{v} θ : 𝓢(E, ℝ)) : E → ℝ))
      (hfc.differentiableAt (by simp)) hθv,
    fderiv_clm_apply hdf (differentiableAt_const v)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add, smul_eq_mul]
  rw [(hfc.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)).eq w v]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

def cutoffPullback (θ : 𝓢(E, ℝ)) : Lp ℝ 2 d.charts.measure →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (cutoffL2 θ (L.region_open a).measurableSet).comp
    (ChartLpNative.chartPullbackL2 (L.chart a) (L.region_open a).measurableSet
      (L.region_subset_target a) (L.lowerConstant_pos a) (L.region_measure_lower a))

theorem cutoffPullback_toLp_coe (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a))
    {f : M → ℝ} (hf : MemLp f 2 d.charts.measure) :
    cutoffPullback d L a θ (hf.toLp f) =ᵐ[volume]
      fun x => θ x * f ((L.chart a).symm x) := by
  have hp := ChartLpNative.chartPullbackL2_toLp_coe (L.chart a)
    (L.region_open a).measurableSet (L.region_subset_target a)
    (L.lowerConstant_pos a) (L.region_measure_lower a) hf
  filter_upwards [cutoffL2_coe θ (L.region_open a).measurableSet
    (hθ.trans (L.scalarCutoff_tsupport_subset a))
    (ChartLpNative.chartPullbackL2 (L.chart a) (L.region_open a).measurableSet
      (L.region_subset_target a) (L.lowerConstant_pos a) (L.region_measure_lower a) (hf.toLp f)),
    (ae_restrict_iff' (L.region_open a).measurableSet).mp hp] with x hcut hpx
  apply hcut.trans
  by_cases hx : x ∈ L.region a
  · exact congrArg (fun q : ℝ => θ x * q) (hpx hx)
  · have hz : θ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (L.scalarCutoff_tsupport_subset a (hθ ht)))
    simp only [hz, zero_mul]

theorem cutoffPullback_value_into_coe (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    cutoffPullback d L a θ (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h))
      =ᵐ[volume] fun x => θ x * scalarProbe d.fields h ab ((L.chart a).symm x) := by
  let hf := pairing_memLp d.fields d.charts.measure h ab.1 ab.2
  have heq : d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h) =
      hf.toLp (scalarProbe d.fields h ab) := by
    apply Lp.ext
    exact (d.valueCoefficient_into_coe ab h).trans hf.coeFn_toLp.symm
  rw [heq]
  exact cutoffPullback_toLp_coe d L a θ hθ hf

theorem cutoffPullback_derivative_into_coe (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a)) (r : Fin d.fieldCount)
    (ab : d.ProbeIndex) (h : SmoothTensor (n := n) (M := M)) :
    cutoffPullback d L a θ
      (d.derivativeCoefficient r ab (intoFirstOrderGraph d.fields d.charts.measure h))
      =ᵐ[volume] fun x => θ x *
        scalarDirectional (d.fields r) (scalarProbe d.fields h ab) ((L.chart a).symm x) := by
  let hf := directional_pairing_memLp d.fields d.charts.measure h r ab.1 ab.2
  have heq : d.derivativeCoefficient r ab (intoFirstOrderGraph d.fields d.charts.measure h) =
      hf.toLp (scalarDirectional (d.fields r) (scalarProbe d.fields h ab)) := by
    apply Lp.ext
    exact (d.derivativeCoefficient_into_coe r ab h).trans hf.coeFn_toLp.symm
  rw [heq]
  exact cutoffPullback_toLp_coe d L a θ hθ hf

theorem firstOrderCutoff_pairing {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : E} (hx : x ∈ (L.chart a).target) :
    (∑ r : Fin d.fieldCount, firstOrderCutoff d L a r x *
      scalarDirectional (d.fields r) f ((L.chart a).symm x)) =
    L.scalarCutoff a x * (∑ j : Fin n, driftCoefficient d a.val.1.val j x *
      fderiv ℝ (f ∘ (L.chart a).symm) x ((PiLp.basisFun 2 ℝ (Fin n)) j)) -
    ∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
      ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (L.scalarCutoff a)) x *
        fderiv ℝ (f ∘ (L.chart a).symm) x ((PiLp.basisFun 2 ℝ (Fin n)) j) +
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} (L.scalarCutoff a)) x *
        fderiv ℝ (f ∘ (L.chart a).symm) x ((PiLp.basisFun 2 ℝ (Fin n)) i)) := by
  let D (r : Fin d.fieldCount) := scalarDirectional (d.fields r) f ((L.chart a).symm x)
  let C (j : Fin n) (r : Fin d.fieldCount) :=
    chartParsevalCoefficient g d.fields a.val.1.val j r x
  have hcoord (j : Fin n) :
      fderiv ℝ (f ∘ (L.chart a).symm) x ((PiLp.basisFun 2 ℝ (Fin n)) j) =
        ∑ r, C j r * D r :=
    coordinate_derivative_eq_parseval g d.fields d.parseval a.val.1.val hf hx j
  have hrow (b : Fin n → ℝ) :
      (∑ r, (∑ j, b j * C j r) * D r) = ∑ j, b j * (∑ r, C j r * D r) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [firstOrderCutoff_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = L.scalarCutoff a x *
          ∑ r, (∑ j, driftCoefficient d a.val.1.val j x * C j r) * D r := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
      _ = _ := by rw [hrow]; simp_rw [hcoord]
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [hcoord, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [C, D]
    ring


theorem localizedSchwartz_principal (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) (x : E) :
    -(∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (d.localizedSchwartz L a ab h))) x) =
    L.scalarCutoff a x *
      scalarLaplacian d.fields d.charts (scalarProbe d.fields h ab) ((L.chart a).symm x) +
    zeroOrderCutoff d L a x * scalarProbe d.fields h ab ((L.chart a).symm x) +
    ∑ r : Fin d.fieldCount, firstOrderCutoff d L a r x *
      scalarDirectional (d.fields r) (scalarProbe d.fields h ab) ((L.chart a).symm x) := by
  by_cases hx : x ∈ (L.chart a).target
  · have hq := scalarProbe_contMDiff d.fields h ab
    have hqchart := contDiffOn_scalar_chartInverse a.val.1.val hq
    have hprincipal := scalarLaplacian_chart_principal d.fields d.charts g d.parseval
      a.val.1.val hq.contMDiffOn hx
    change scalarLaplacian d.fields d.charts (scalarProbe d.fields h ab)
        ((chartAt E a.val.1.val).symm x) =
      -(∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
        fderiv ℝ (fderiv ℝ (scalarProbe d.fields h ab ∘ (chartAt E a.val.1.val).symm)) x
          ((PiLp.basisFun 2 ℝ (Fin n)) i) ((PiLp.basisFun 2 ℝ (Fin n)) j)) -
        scalarChartLowerTerm d.fields d.charts a.val.1.val (scalarProbe d.fields h ab) x
      at hprincipal
    have hfirst := firstOrderCutoff_pairing d L a hq hx
    have hlocal := localizedSchwartz_eq_cutoffCoefficient d L a ab h
    dsimp only [FiniteChartLocalizationData.chart, FiniteChartData.chart] at hfirst hlocal ⊢
    rw [hprincipal, scalarChartLowerTerm_eq, zeroOrderCutoff_apply,
      hfirst, hlocal]
    simp_rw [cutoffCoefficient_secondLineDeriv_apply d L a _ _ _ hqchart hx]
    simp only [Function.comp_apply, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm]
    ring
  · have hxs : x ∉ tsupport (L.scalarCutoff a) :=
      fun ht => hx (cutoff_support_target d L a ht)
    have hz := image_eq_zero_of_notMem_tsupport hxs
    have hzero := image_eq_zero_of_notMem_tsupport
      (fun ht => hxs (zeroOrderCutoff_support d L a ht))
    have hfirst (r : Fin d.fieldCount) := image_eq_zero_of_notMem_tsupport
      (fun ht => hxs (firstOrderCutoff_support d L a r ht))
    have hsecond (i j : Fin n) :
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (d.localizedSchwartz L a ab h))) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hxs
        (localizedSchwartz_support d L a ab h
          (SchwartzMap.tsupport_lineDerivOp_subset _ _
            (SchwartzMap.tsupport_lineDerivOp_subset _ _ ht))))
    simp only [hz, hzero, hfirst, hsecond, mul_zero, zero_mul, Finset.sum_const_zero,
      neg_zero, add_zero, zero_add]


def lowerSource (ab : d.ProbeIndex) : d.Form →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (L.localizationL2 a).comp (d.lowerSource ab) +
    (cutoffPullback d L a (zeroOrderCutoff d L a)).comp ((d.valueCoefficient ab).comp d.inclusion) +
    ∑ r : Fin d.fieldCount,
      (cutoffPullback d L a (firstOrderCutoff d L a r)).comp (d.derivativeCoefficient r ab)

theorem lowerSource_into_coe (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    lowerSource d L a ab (intoFirstOrderGraph d.fields d.charts.measure h) =ᵐ[volume]
      fun x => L.scalarCutoff a x *
        projectionLowerSource d.fields d.charts g ((L.chart a).symm x)
          (probes d.fields h ((L.chart a).symm x))
          (derivativeProbes d.fields h ((L.chart a).symm x)) ab +
        zeroOrderCutoff d L a x * scalarProbe d.fields h ab ((L.chart a).symm x) +
        ∑ r : Fin d.fieldCount, firstOrderCutoff d L a r x *
          scalarDirectional (d.fields r) (scalarProbe d.fields h ab) ((L.chart a).symm x) := by
  let z := intoFirstOrderGraph d.fields d.charts.measure h
  let p : M → ℝ := fun x => projectionLowerSource d.fields d.charts g x
    (probes d.fields h x) (derivativeProbes d.fields h x) ab
  have hp : MemLp p 2 d.charts.measure :=
    (Lp.memLp (d.lowerSource ab z)).ae_eq (d.lowerSource_into_coe ab h)
  have hpEq : d.lowerSource ab z = hp.toLp p := by
    apply Lp.ext
    exact (d.lowerSource_into_coe ab h).trans hp.coeFn_toLp.symm
  have hloc := L.localizationL2_toLp_coe a hp
  rw [← hpEq] at hloc
  let V := cutoffPullback d L a (zeroOrderCutoff d L a)
    (d.valueCoefficient ab (intoTensorL2 d.fields d.charts.measure h))
  let D (r : Fin d.fieldCount) := cutoffPullback d L a (firstOrderCutoff d L a r)
    (d.derivativeCoefficient r ab z)
  simp only [lowerSource, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, TensorHilbertNative.Data.inclusion, graphValue_into]
  change (L.localizationL2 a (d.lowerSource ab z) + V + ∑ r, D r) =ᵐ[volume] _
  filter_upwards [hloc,
    cutoffPullback_value_into_coe d L a (zeroOrderCutoff d L a)
      (zeroOrderCutoff_support d L a) ab h,
    ae_all_iff.mpr (fun r => cutoffPullback_derivative_into_coe d L a
      (firstOrderCutoff d L a r) (firstOrderCutoff_support d L a r) r ab h),
    Lp.coeFn_add (L.localizationL2 a (d.lowerSource ab z)) V,
    Lp.coeFn_add (L.localizationL2 a (d.lowerSource ab z) + V) (∑ r, D r),
    Lp.coeFn_fun_finsetSum Finset.univ D] with x hpv hv hd hadd hadd' hsum
  rw [hadd', Pi.add_apply, hadd, Pi.add_apply, hsum, hpv, hv]
  congr 1
  exact Finset.sum_congr rfl (fun r _ => hd r)

theorem generatorSource_into_coe (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    (L.localizationL2 a (d.valueCoefficient ab
      (intoTensorL2 d.fields d.charts.measure (smoothTensorLaplacian d.fields d.charts g h))) +
      lowerSource d L a ab (intoFirstOrderGraph d.fields d.charts.measure h)) =ᵐ[volume]
      fun x => -(∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} (d.localizedSchwartz L a ab h))) x) := by
  have hloc := cutoffPullback_value_into_coe d L a (L.scalarCutoff a)
    (Subset.refl _) ab (smoothTensorLaplacian d.fields d.charts g h)
  change L.localizationL2 a (d.valueCoefficient ab
    (intoTensorL2 d.fields d.charts.measure (smoothTensorLaplacian d.fields d.charts g h)))
      =ᵐ[volume] _ at hloc
  filter_upwards [hloc, lowerSource_into_coe d L a ab h,
    Lp.coeFn_add
      (L.localizationL2 a (d.valueCoefficient ab
        (intoTensorL2 d.fields d.charts.measure (smoothTensorLaplacian d.fields d.charts g h))))
      (lowerSource d L a ab (intoFirstOrderGraph d.fields d.charts.measure h))]
      with x hl hs hadd
  rw [hadd, Pi.add_apply, hl, hs, localizedSchwartz_principal,
    scalarLaplacian_probe_eq d.fields d.charts g d.parseval h ab]
  change _ = L.scalarCutoff a x * (scalarProbe d.fields
    (smoothTensorLaplacian d.fields d.charts g h) ab ((L.chart a).symm x) + _) + _ + _
  ring


def principalAdjointTest (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) : 𝓢(E, ℝ) :=
  -∑ i : Fin n, ∑ j : Fin n,
    ∂_{(PiLp.basisFun 2 ℝ (Fin n)) i}
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
        (cutoffSchwartz φ hφ (L.chart a).open_target hφU
          (principalCoefficient g a.val.1.val i j)
          (principalCoefficient_contDiffOn g a.val.1.val i j)))

theorem inner_principalAdjointTest (f φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) :
    inner ℝ (f.toLp 2 volume) ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume) =
      ∫ x, -(∑ i : Fin n, ∑ j : Fin n, principalCoefficient g a.val.1.val i j x *
        (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} f)) x) * φ x := by
  let b (i j : Fin n) : 𝓢(E, ℝ) :=
    cutoffSchwartz φ hφ (L.chart a).open_target hφU
      (principalCoefficient g a.val.1.val i j)
      (principalCoefficient_contDiffOn g a.val.1.val i j)
  let D (i j : Fin n) : 𝓢(E, ℝ) :=
    ∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
      (∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} f)
  have hi (i j : Fin n) : Integrable (fun x => D i j x * b i j x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (D i j) (b i j)).integrable
  have hibp (i j : Fin n) :
      inner ℝ (f.toLp 2 volume)
        ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) i}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} (b i j))).toLp 2 volume) =
      ∫ x, D i j x * b i j x := by
    rw [inner_schwartzLineDeriv, inner_schwartzLineDeriv, neg_neg,
      inner_schwartzToLp]
  calc
    _ = -(∑ i : Fin n, ∑ j : Fin n, ∫ x, D i j x * b i j x) := by
      change inner ℝ (SchwartzMap.toLpCLM ℝ ℝ 2 volume f)
        (SchwartzMap.toLpCLM ℝ ℝ 2 volume
          (-∑ i : Fin n, ∑ j : Fin n,
            ∂_{(PiLp.basisFun 2 ℝ (Fin n)) i}
              (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} (b i j)))) = _
      simp only [map_neg, map_sum, inner_neg_right, inner_sum,
        SchwartzMap.toLpCLM_apply, hibp]
    _ = -(∫ x, ∑ i : Fin n, ∑ j : Fin n, D i j x * b i j x) := by
      rw [integral_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j)]
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [b, cutoffSchwartz_apply, D, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem localized_principal_pairing_smooth (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) (φ : 𝓢(E, ℝ))
    (hφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ (L.chart a).target) :
    inner ℝ (d.localizedValue L a ab (intoFirstOrderGraph d.fields d.charts.measure h))
      ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume) =
    inner ℝ
      (L.localizationL2 a (d.valueCoefficient ab
        (intoTensorL2 d.fields d.charts.measure (smoothTensorLaplacian d.fields d.charts g h))) +
        lowerSource d L a ab (intoFirstOrderGraph d.fields d.charts.measure h))
      (φ.toLp 2 volume) := by
  rw [d.localizedValue_into, inner_principalAdjointTest, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [generatorSource_into_coe d L a ab h, φ.coeFn_toLp 2 volume]
    with x hsource htest
  rw [hsource, htest, Real.inner_apply]


theorem localized_principal_pairing_form (ab : d.ProbeIndex) (z : d.Form)
    (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) :
    inner ℝ (d.localizedValue L a ab z)
      ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume) =
    inner ℝ (intoFirstOrderGraph d.fields d.charts.measure (densityTensorTest d L a ab φ)) z -
      inner ℝ (intoTensorL2 d.fields d.charts.measure (densityTensorTest d L a ab φ))
        (d.inclusion z) +
      inner ℝ (lowerSource d L a ab z) (φ.toLp 2 volume) := by
  have heq :
      (fun z : d.Form => inner ℝ (d.localizedValue L a ab z)
        ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume)) =
      (fun z : d.Form =>
        inner ℝ (intoFirstOrderGraph d.fields d.charts.measure (densityTensorTest d L a ab φ)) z -
          inner ℝ (intoTensorL2 d.fields d.charts.measure (densityTensorTest d L a ab φ))
            (d.inclusion z) +
          inner ℝ (lowerSource d L a ab z) (φ.toLp 2 volume)) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((d.localizedValue L a ab).continuous.inner continuous_const)
      (((continuous_const.inner continuous_id).sub
        (continuous_const.inner d.inclusion.continuous)).add
          ((lowerSource d L a ab).continuous.inner continuous_const))
    funext h
    dsimp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, id_eq]
    rw [localized_principal_pairing_smooth, inner_add_left]
    have hform := form_pairing_laplacian d.fields d.charts g d.parseval h
      (intoFirstOrderGraph d.fields d.charts.measure (densityTensorTest d L a ab φ))
    rw [graphValue_into, inner_add_right,
      densityTensorTest_pairing d L a ab φ] at hform
    change _ = inner ℝ
      (intoFirstOrderGraph d.fields d.charts.measure (densityTensorTest d L a ab φ))
      (intoFirstOrderGraph d.fields d.charts.measure h) -
      inner ℝ (intoTensorL2 d.fields d.charts.measure (densityTensorTest d L a ab φ))
        (intoTensorL2 d.fields d.charts.measure h) + _
    rw [densityTensorTest_pairing d L a ab φ]
    rw [densityTensorTest_pairing d L a ab φ] at hform
    linarith only [hform]
  exact congrFun heq z



theorem generatorGraph_localized_equation {u b : d.Value} (hb : d.GeneratorGraph u b) :
    ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
      ∀ (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
        (hφU : tsupport φ ⊆ (L.chart a).target),
        inner ℝ (L.localizationL2 a (d.valueCoefficient ab u))
          ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume) =
        inner ℝ (L.localizationL2 a (d.valueCoefficient ab b) + lowerSource d L a ab z)
          (φ.toLp 2 volume) := by
  obtain ⟨z, hz, hform⟩ := (d.generatorGraph_iff_variational u b).mp hb
  refine ⟨z, hz, d.norm_form_le_of_variational hz hform, ?_⟩
  intro ab φ hφ hφU
  have hid := localized_principal_pairing_form d L a ab z φ hφ hφU
  have htest := hform (intoFirstOrderGraph d.fields d.charts.measure
    (densityTensorTest d L a ab φ))
  change inner ℝ (intoFirstOrderGraph d.fields d.charts.measure
    (densityTensorTest d L a ab φ)) z =
      inner ℝ (intoTensorL2 d.fields d.charts.measure (densityTensorTest d L a ab φ)) (u + b)
    at htest
  rw [inner_add_right] at htest
  change inner ℝ (L.localizationL2 a (d.valueCoefficient ab (d.inclusion z))) _ = _ at hid
  rw [hz, htest, add_sub_cancel_left, densityTensorTest_pairing d L a ab φ,
    ← inner_add_left] at hid
  exact hid


theorem localizedDerivative_pairing (ab : d.ProbeIndex) (z : d.Form)
    (i : Fin n) (φ : 𝓢(E, ℝ)) :
    inner ℝ (d.localizedValue L a ab z)
      ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} φ).toLp 2 volume) =
      -inner ℝ (d.localizedDerivative L a ab i z) (φ.toLp 2 volume) := by
  have heq :
      (fun z : d.Form => inner ℝ (d.localizedValue L a ab z)
        ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) i} φ).toLp 2 volume)) =
      (fun z : d.Form => -inner ℝ (d.localizedDerivative L a ab i z) (φ.toLp 2 volume)) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((d.localizedValue L a ab).continuous.inner continuous_const)
      (((d.localizedDerivative L a ab i).continuous.inner continuous_const).neg)
    funext h
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [d.localizedValue_into, d.localizedDerivative_into]
    simpa only [PiLp.basisFun_apply] using
      inner_schwartzLineDeriv (d.localizedSchwartz L a ab h) φ (EuclideanSpace.single i 1)
  exact congrFun heq z


theorem principalAdjointTest_firstOrder_pairing (ab : d.ProbeIndex) (z : d.Form)
    (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) :
    inner ℝ (d.localizedValue L a ab z)
      ((principalAdjointTest d L a φ hφ hφU).toLp 2 volume) =
      ∑ i : Fin n, ∑ j : Fin n, inner ℝ (d.localizedDerivative L a ab i z)
        ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
          (cutoffSchwartz φ hφ (L.chart a).open_target hφU
            (principalCoefficient g a.val.1.val i j)
            (principalCoefficient_contDiffOn g a.val.1.val i j))).toLp 2 volume) := by
  change inner ℝ (d.localizedValue L a ab z)
    (SchwartzMap.toLpCLM ℝ ℝ 2 volume
      (-∑ i : Fin n, ∑ j : Fin n,
        ∂_{(PiLp.basisFun 2 ℝ (Fin n)) i}
          (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
            (cutoffSchwartz φ hφ (L.chart a).open_target hφU
              (principalCoefficient g a.val.1.val i j)
              (principalCoefficient_contDiffOn g a.val.1.val i j))))) = _
  simp only [map_neg, map_sum, inner_neg_right, inner_sum,
    SchwartzMap.toLpCLM_apply, localizedDerivative_pairing,
    Finset.sum_neg_distrib, neg_neg]


theorem generatorGraph_firstOrder_equation {u b : d.Value} (hb : d.GeneratorGraph u b) :
    ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
      ∀ (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
        (hφU : tsupport φ ⊆ (L.chart a).target),
        (∑ i : Fin n, ∑ j : Fin n, inner ℝ (d.localizedDerivative L a ab i z)
          ((∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
            (cutoffSchwartz φ hφ (L.chart a).open_target hφU
              (principalCoefficient g a.val.1.val i j)
              (principalCoefficient_contDiffOn g a.val.1.val i j))).toLp 2 volume)) =
          inner ℝ (L.localizationL2 a (d.valueCoefficient ab b) + lowerSource d L a ab z)
            (φ.toLp 2 volume) := by
  obtain ⟨z, hz, hnorm, heq⟩ := generatorGraph_localized_equation d L a hb
  refine ⟨z, hz, hnorm, ?_⟩
  intro ab φ hφ hφU
  rw [← principalAdjointTest_firstOrder_pairing]
  change inner ℝ (L.localizationL2 a (d.valueCoefficient ab (d.inclusion z))) _ = _
  rw [hz]
  exact heq ab φ hφ hφU

theorem principalCoefficientDerivative_contDiffOn (i j : Fin n) :
    ContDiffOn ℝ ∞
      (fun x => fderiv ℝ (principalCoefficient g a.val.1.val i j) x
        ((PiLp.basisFun 2 ℝ (Fin n)) j)) (L.chart a).target :=
  ((principalCoefficient_contDiffOn g a.val.1.val i j).fderiv_of_isOpen
    (L.chart a).open_target (by simp)).clm_apply contDiffOn_const

def principalFluxTest (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) (i j : Fin n) : 𝓢(E, ℝ) :=
  cutoffSchwartz (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} φ)
    (hφ.of_isClosed_subset (isClosed_tsupport _)
      (SchwartzMap.tsupport_lineDerivOp_subset _ _))
    (L.chart a).open_target ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hφU)
    (principalCoefficient g a.val.1.val i j) (principalCoefficient_contDiffOn g a.val.1.val i j)

def principalGradientTest (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) (i j : Fin n) : 𝓢(E, ℝ) :=
  cutoffSchwartz φ hφ (L.chart a).open_target hφU
    (fun x => fderiv ℝ (principalCoefficient g a.val.1.val i j) x
      ((PiLp.basisFun 2 ℝ (Fin n)) j))
    (principalCoefficientDerivative_contDiffOn d L a i j)


theorem principalProduct_deriv (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) (i j : Fin n) :
    (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
      (cutoffSchwartz φ hφ (L.chart a).open_target hφU
        (principalCoefficient g a.val.1.val i j)
        (principalCoefficient_contDiffOn g a.val.1.val i j))) =
      principalFluxTest d L a φ hφ hφU i j + principalGradientTest d L a φ hφ hφU i j := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => φ y * principalCoefficient g a.val.1.val i j y) x
      ((PiLp.basisFun 2 ℝ (Fin n)) j) =
    (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j} φ) x * principalCoefficient g a.val.1.val i j x +
      φ x * fderiv ℝ (principalCoefficient g a.val.1.val i j) x
        ((PiLp.basisFun 2 ℝ (Fin n)) j)
  rw [fderiv_cutoff_mul φ (L.chart a).open_target hφU
    (principalCoefficient_contDiffOn g a.val.1.val i j),
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

theorem principalProduct_deriv_toLp (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (L.chart a).target) (i j : Fin n) :
    (∂_{(PiLp.basisFun 2 ℝ (Fin n)) j}
      (cutoffSchwartz φ hφ (L.chart a).open_target hφU
        (principalCoefficient g a.val.1.val i j)
        (principalCoefficient_contDiffOn g a.val.1.val i j))).toLp 2 volume =
      (principalFluxTest d L a φ hφ hφU i j).toLp 2 volume +
        (principalGradientTest d L a φ hφ hφU i j).toLp 2 volume := by
  change SchwartzMap.toLpCLM ℝ ℝ 2 volume _ = _
  rw [principalProduct_deriv, map_add]
  rfl


theorem generatorGraph_divergence_equation {u b : d.Value} (hb : d.GeneratorGraph u b) :
    ∃ z : d.Form, d.inclusion z = u ∧ ‖z‖ ≤ ‖u‖ + ‖b‖ ∧
      ∀ (ab : d.ProbeIndex) (φ : 𝓢(E, ℝ)) (hφ : HasCompactSupport φ)
        (hφU : tsupport φ ⊆ (L.chart a).target),
        (∑ i : Fin n, ∑ j : Fin n, inner ℝ (d.localizedDerivative L a ab i z)
          ((principalFluxTest d L a φ hφ hφU i j).toLp 2 volume)) =
          inner ℝ (L.localizationL2 a (d.valueCoefficient ab b) + lowerSource d L a ab z)
            (φ.toLp 2 volume) -
            ∑ i : Fin n, ∑ j : Fin n, inner ℝ (d.localizedDerivative L a ab i z)
              ((principalGradientTest d L a φ hφ hφU i j).toLp 2 volume) := by
  obtain ⟨z, hz, hnorm, heq⟩ := generatorGraph_firstOrder_equation d L a hb
  refine ⟨z, hz, hnorm, ?_⟩
  intro ab φ hφ hφU
  have h := heq ab φ hφ hφU
  simp only [principalProduct_deriv_toLp, inner_add_right, Finset.sum_add_distrib] at h
  exact eq_sub_iff_add_eq.mpr h


theorem localizedSchwartz_support_cutoff (ab : d.ProbeIndex)
    (h : SmoothTensor (n := n) (M := M)) :
    tsupport (d.localizedSchwartz L a ab h) ⊆ tsupport (L.scalarCutoff a) := by
  have hprod : (d.localizedSchwartz L a ab h : E → ℝ) =
      fun x => L.scalarCutoff a x * scalarProbe d.fields h ab ((L.chart a).symm x) := by
    funext x
    rw [d.localizedSchwartz_apply, L.scalarCutoff_apply]
    by_cases hx : x ∈ (L.chart a).target
    · rw [chartScalar_of_mem _ _ hx, chartScalar_of_mem _ _ hx]
      rfl
    · rw [chartScalar_of_notMem _ _ hx, chartScalar_of_notMem _ _ hx, zero_mul]
  rw [hprod]
  exact tsupport_mul_subset_left


theorem schwartzMultiplier_localizedDerivative (ab : d.ProbeIndex) (i : Fin n)
    (η : 𝓢(E, ℝ)) (hη : ∀ x ∈ tsupport (L.scalarCutoff a), η x = 1) (z : d.Form) :
    schwartzMultiplier η (d.localizedDerivative L a ab i z) =
      d.localizedDerivative L a ab i z := by
  have heq :
      (fun z : d.Form => schwartzMultiplier η (d.localizedDerivative L a ab i z)) =
      (fun z : d.Form => d.localizedDerivative L a ab i z) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((schwartzMultiplier η).continuous.comp (d.localizedDerivative L a ab i).continuous)
      (d.localizedDerivative L a ab i).continuous
    funext h
    dsimp only [Function.comp_apply]
    rw [d.localizedDerivative_into]
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe η
      ((∂_{EuclideanSpace.single i (1 : ℝ)} (d.localizedSchwartz L a ab h)).toLp 2 volume),
      (∂_{EuclideanSpace.single i (1 : ℝ)} (d.localizedSchwartz L a ab h)).coeFn_toLp 2 volume]
      with x hmul hderiv
    rw [hmul, hderiv]
    by_cases hx : x ∈ tsupport (L.scalarCutoff a)
    · rw [hη x hx, one_mul]
    · have hz : (∂_{EuclideanSpace.single i (1 : ℝ)} (d.localizedSchwartz L a ab h)) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hx
          (localizedSchwartz_support_cutoff d L a ab h
            (SchwartzMap.tsupport_lineDerivOp_subset _ _ hmem)))
      rw [hz, mul_zero]
  exact congrFun heq z



theorem integrable_localizedDerivative (ab : d.ProbeIndex) (i : Fin n)
    (η : 𝓢(E, ℝ)) (hη : ∀ x ∈ tsupport (L.scalarCutoff a), η x = 1) (z : d.Form) :
    Integrable (d.localizedDerivative L a ab i z : E → ℝ) volume := by
  have hprod : Integrable (fun x => η x * d.localizedDerivative L a ab i z x) volume :=
    (η.memLp 2 volume).integrable_mul (Lp.memLp (d.localizedDerivative L a ab i z))
  have heq := schwartzMultiplier_coe η (d.localizedDerivative L a ab i z)
  rw [schwartzMultiplier_localizedDerivative d L a ab i η hη z] at heq
  exact hprod.congr heq.symm

end PoincareConjecture.NativeLocalizedEllipticEquationNative
