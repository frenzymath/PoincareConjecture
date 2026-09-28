import PoincareConjecture.Proofs.M03.Existence.DeTurckLocalizedH2Native
import PoincareConjecture.Proofs.M03.Existence.DeTurckHigherDomainNative
import PoincareConjecture.Proofs.M03.Existence.SymmetricTensorHilbertNative









set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped Topology Manifold ContDiff SchwartzMap LineDeriv BigOperators

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNestedLocalizationNative

open ChartMeasureNative TensorHilbertNative TensorProbeNative
  NativeChartScalarLocalization NativeLocalizedEllipticEquationNative
  EuclideanDerivativeNative EuclideanTranslationNative DeTurckHigherDomainNative
  ParsevalTensorNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem sourcePositiveRegion_mono (c : FiniteChartData (n := n) (M := M))
    (p : c.centers) {k l : ℕ} (hkl : k ≤ l) :
    c.sourcePositiveRegion p k ⊆ c.sourcePositiveRegion p l := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hden : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkl 1
  exact (one_div_le_one_div_of_le (by positivity) hden).trans_lt hx.2


theorem exists_localization_weight_one (c : FiniteChartData (n := n) (M := M))
    (L : FiniteChartLocalizationData c) (p : c.centers) (k : ℕ)
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUp : U ⊆ c.sourcePositiveRegion p k) :
    ∃ L' : FiniteChartLocalizationData c, ∃ b : L'.patches,
      b.val.1 = p ∧ tsupport (L'.weight b) ⊆ U ∧ ∀ x ∈ K, L'.weight b x = 1 := by
  classical
  let j : c.centers × ℕ := (p, k + L.patches.sup Prod.snd + 1)
  have hjnot : j ∉ L.patches := by
    intro hj
    have h := Finset.le_sup (f := Prod.snd) hj
    change k + L.patches.sup Prod.snd + 1 ≤ L.patches.sup Prod.snd at h
    omega
  let s : Finset (c.centers × ℕ) := insert j L.patches
  let V : s → Set M := fun i =>
    if i.val = j then U else c.sourcePositiveRegion i.val.1 i.val.2 \ K
  have hVopen (i : s) : IsOpen (V i) := by
    dsimp only [V]
    split_ifs
    · exact hU
    · exact (c.sourcePositiveRegion_open i.val.1 i.val.2).sdiff hK.isClosed
  have hcover : univ ⊆ ⋃ i : s, V i := by
    intro x _
    by_cases hx : x ∈ K
    · refine mem_iUnion.mpr ⟨⟨j, Finset.mem_insert_self _ _⟩, ?_⟩
      simpa only [V, if_pos rfl] using hKU hx
    · obtain ⟨a, ha⟩ := L.partition.exists_pos_of_mem (mem_univ x)
      have hxa : x ∈ c.sourcePositiveRegion a.val.1 a.val.2 :=
        L.support_subset a (subset_tsupport (L.partition a) ha.ne')
      have haj : a.val ≠ j := fun heq => hjnot (heq ▸ a.property)
      refine mem_iUnion.mpr ⟨⟨a.val, Finset.mem_insert_of_mem a.property⟩, ?_⟩
      simpa only [V, if_neg haj, Set.mem_sdiff] using And.intro hxa hx
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    isClosed_univ V hVopen hcover
  have hVregion (i : s) : V i ⊆ c.sourcePositiveRegion i.val.1 i.val.2 := by
    by_cases hi : i.val = j
    · simp only [V, if_pos hi]
      rw [hi]
      exact hUp.trans (sourcePositiveRegion_mono c p (by dsimp only [j]; omega))
    · simp only [V, if_neg hi]
      exact diff_subset
  let L' : FiniteChartLocalizationData c :=
    ⟨s, ψ, fun i => (hψ i).trans (hVregion i)⟩
  let b : L'.patches := ⟨j, Finset.mem_insert_self _ _⟩
  refine ⟨L', b, rfl, ?_, ?_⟩
  · simpa only [L', b, FiniteChartLocalizationData.weight, ContinuousMap.coe_mk,
      V, if_pos rfl] using hψ b
  · intro x hx
    have hzero (i : L'.patches) (hi : i ≠ b) : L'.weight i x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hij : i.val ≠ j := fun heq => hi (Subtype.ext heq)
      have hiK := hψ i hmem
      simpa only [V, if_neg hij, mem_diff, not_true_eq_false, and_false, hx] using hiK
    have hsum : (∑ i : L'.patches, L'.weight i x) = L'.weight b x := by
      apply Finset.sum_eq_single b
      · intro i _ hi
        exact hzero i hi
      · intro hb
        exact False.elim (hb (Finset.mem_univ b))
    exact hsum.symm.trans (L'.weight_sum x)

variable [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric n M} (d : TensorHilbertNative.Data g)
  (L : FiniteChartLocalizationData d.charts) (a : L.patches)


theorem exists_nested_localization :
    ∃ L' : FiniteChartLocalizationData d.charts, ∃ b : L'.patches,
      b.val.1 = a.val.1 ∧
        ∀ x ∈ tsupport (L.scalarCutoff a), L'.scalarCutoff b x = 1 := by
  obtain ⟨L', b, hcenter, _, hone⟩ := exists_localization_weight_one d.charts L
    a.val.1 a.val.2 (L.weight_compactSupport a)
    (d.charts.sourcePositiveRegion_open a.val.1 a.val.2)
    (L.support_subset a) (Subset.refl _)
  refine ⟨L', b, hcenter, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_chartScalar_subset a.val.1.val
    (L.weight_compactSupport a) (L.weight_support_source a)
    (L.weight_zero_off_support a) hx
  have hychart := L.weight_support_source a hy
  have hcenter' : b.val.1.val = a.val.1.val := congrArg Subtype.val hcenter
  rw [L'.scalarCutoff_apply, hcenter', chartScalar_of_mem _ _
    ((chartAt E a.val.1.val).mapsTo hychart),
    (chartAt E a.val.1.val).left_inv hychart]
  exact hone y hy


theorem cutoffPullback_eq_multiplier_localization
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1) (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a))
    (hone : ∀ x ∈ tsupport θ, L'.scalarCutoff b x = 1)
    (f : Lp ℝ 2 d.charts.measure) :
    cutoffPullback d L a θ f = schwartzMultiplier θ (L'.localizationL2 b f) := by
  have hchart : L'.chart b = L.chart a := by
    simp only [FiniteChartLocalizationData.chart, hcenter]
  have hp := cutoffPullback_toLp_coe d L a θ hθ (Lp.memLp f)
  have hfto : (Lp.memLp f).toLp f = f := by
    apply Lp.ext
    exact (Lp.memLp f).coeFn_toLp
  rw [hfto] at hp
  apply Lp.ext
  filter_upwards [hp, schwartzMultiplier_coe θ (L'.localizationL2 b f),
    L'.localizationL2_coe b f] with x hleft hright hloc
  rw [hleft, hright, hloc, hchart]
  by_cases hx : x ∈ tsupport θ
  · rw [hone x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]


theorem cutoffPullback_value_eq (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1) (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a))
    (hone : ∀ x ∈ tsupport θ, L'.scalarCutoff b x = 1)
    (ab : d.ProbeIndex) (z : d.Form) :
    cutoffPullback d L a θ (d.valueCoefficient ab (d.inclusion z)) =
      schwartzMultiplier θ (d.localizedValue L' b ab z) :=
  cutoffPullback_eq_multiplier_localization d L a L' b hcenter θ hθ hone _

private theorem localizedSchwartz_fderiv_eq_of_cutoff_ne_zero
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1) (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a))
    (hone : ∀ x ∈ tsupport θ, L'.scalarCutoff b x = 1)
    (ab : d.ProbeIndex) (h : SmoothTensor (n := n) (M := M))
    {x : E} (hx : θ x ≠ 0) :
    fderiv ℝ (d.localizedSchwartz L' b ab h) x =
      fderiv ℝ (scalarProbe d.fields h ab ∘ (L.chart a).symm) x := by
  have hchart : L'.chart b = L.chart a := by
    simp only [FiniteChartLocalizationData.chart, hcenter]
  have heq : (d.localizedSchwartz L' b ab h : E → ℝ) =ᶠ[𝓝 x]
      scalarProbe d.fields h ab ∘ (L.chart a).symm := by
    filter_upwards [θ.continuous.isOpen_support.mem_nhds hx] with y hy
    have hyθ : y ∈ tsupport θ := subset_tsupport θ hy
    have hyt : y ∈ (L'.chart b).target := by
      rw [hchart]
      exact L.region_subset_target a (L.scalarCutoff_tsupport_subset a (hθ hyθ))
    have hone' := hone y hyθ
    rw [L'.scalarCutoff_apply, chartScalar_of_mem _ _ hyt] at hone'
    change L'.weight b ((L'.chart b).symm y) = 1 at hone'
    rw [d.localizedSchwartz_apply, chartScalar_of_mem _ _ hyt]
    change L'.weight b ((L'.chart b).symm y) *
      scalarProbe d.fields h ab ((L'.chart b).symm y) =
      scalarProbe d.fields h ab ((L.chart a).symm y)
    rw [hone', one_mul, hchart]
  exact heq.fderiv_eq



theorem cutoffPullback_derivative_eq
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1) (θ : 𝓢(E, ℝ))
    (hθ : tsupport θ ⊆ tsupport (L.scalarCutoff a))
    (hone : ∀ x ∈ tsupport θ, L'.scalarCutoff b x = 1)
    (r : Fin d.fieldCount) (ab : d.ProbeIndex) (z : d.Form) :
    cutoffPullback d L a θ (d.derivativeCoefficient r ab z) =
      ∑ j : Fin n, schwartzMultiplier
        (cutoffCoefficient d L a θ hθ
          (fun x => chartField a.val.1.val (d.fields r) x j)
          (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j))
        (d.localizedDerivative L' b ab j z) := by
  let A : Fin n → 𝓢(E, ℝ) := fun j => cutoffCoefficient d L a θ hθ
    (fun x => chartField a.val.1.val (d.fields r) x j)
    (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j)
  have heq :
      (fun z : d.Form => cutoffPullback d L a θ (d.derivativeCoefficient r ab z)) =
      (fun z : d.Form => ∑ j : Fin n,
        schwartzMultiplier (A j) (d.localizedDerivative L' b ab j z)) := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((cutoffPullback d L a θ).continuous.comp (d.derivativeCoefficient r ab).continuous)
    · apply continuous_finset_sum
      intro j _
      exact (schwartzMultiplier (A j)).continuous.comp
        (d.localizedDerivative L' b ab j).continuous
    funext h
    change cutoffPullback d L a θ (d.derivativeCoefficient r ab
      (intoFirstOrderGraph d.fields d.charts.measure h)) =
        ∑ j : Fin n, schwartzMultiplier (A j) (d.localizedDerivative L' b ab j
          (intoFirstOrderGraph d.fields d.charts.measure h))
    have hterm (j : Fin n) :
        schwartzMultiplier (A j) (d.localizedDerivative L' b ab j
          (intoFirstOrderGraph d.fields d.charts.measure h)) =ᵐ[volume]
          fun x => A j x * fderiv ℝ (d.localizedSchwartz L' b ab h) x
            (EuclideanSpace.single j 1) := by
      rw [d.localizedDerivative_into]
      filter_upwards [schwartzMultiplier_coe (A j)
        ((∂_{EuclideanSpace.single j (1 : ℝ)} (d.localizedSchwartz L' b ab h)).toLp 2 volume),
        (∂_{EuclideanSpace.single j (1 : ℝ)} (d.localizedSchwartz L' b ab h)).coeFn_toLp 2 volume]
        with x hmul hderiv
      rw [hmul, hderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    apply Lp.ext
    filter_upwards [cutoffPullback_derivative_into_coe d L a θ hθ r ab h,
      Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin n =>
        schwartzMultiplier (A j) (d.localizedDerivative L' b ab j
          (intoFirstOrderGraph d.fields d.charts.measure h))),
      ae_all_iff.mpr hterm] with x hleft hsum hterms
    rw [hleft, hsum]
    simp_rw [hterms]
    by_cases hx : θ x = 0
    · simp only [A, cutoffCoefficient_apply, hx, zero_mul, Finset.sum_const_zero]
    · have hderiv := localizedSchwartz_fderiv_eq_of_cutoff_ne_zero d L a
        L' b hcenter θ hθ hone ab h hx
      have hxt : x ∈ (chartAt E a.val.1.val).target :=
        cutoff_support_target d L a (hθ (subset_tsupport θ hx))
      have hdirection := directional_eq_chart_firstOrder a.val.1.val (d.fields r)
        (scalarProbe_contMDiff d.fields h ab) hxt
      change scalarDirectional (d.fields r) (scalarProbe d.fields h ab)
          ((L.chart a).symm x) = _ at hdirection
      rw [hdirection, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [A, cutoffCoefficient_apply, hderiv, PiLp.basisFun_apply,
        FiniteChartLocalizationData.chart, FiniteChartData.chart, EuclideanSpace.single]
      ring
  exact congrFun heq z


def projectionValueCutoff (ab cd : d.ProbeIndex) : 𝓢(E, ℝ) :=
  cutoffCoefficient d L a (L.scalarCutoff a) (Subset.refl _)
    (scalarLaplacian d.fields d.charts
      (fun y => projectionKernel g d.fields y ab cd) ∘ (L.chart a).symm)
    (contDiffOn_scalar_chartInverse a.val.1.val
      (scalarLaplacian_contMDiff d.fields d.charts
        (projectionKernel_contMDiff d.fields g ab cd)))


def projectionDerivativeCutoff (ab cd : d.ProbeIndex) (r : Fin d.fieldCount) : 𝓢(E, ℝ) :=
  cutoffCoefficient d L a (L.scalarCutoff a) (Subset.refl _)
    (fun x => -2 * scalarDirectional (d.fields r)
      (fun y => projectionKernel g d.fields y ab cd) ((L.chart a).symm x))
    (contDiffOn_const.mul (contDiffOn_scalar_chartInverse a.val.1.val
      (contMDiff_directional (projectionKernel_contMDiff d.fields g ab cd)
        (d.fields r))))

theorem projectionValueCutoff_support (ab cd : d.ProbeIndex) :
    tsupport (projectionValueCutoff d L a ab cd) ⊆ tsupport (L.scalarCutoff a) :=
  cutoffCoefficient_support d L a _ _ _ _

theorem projectionDerivativeCutoff_support (ab cd : d.ProbeIndex)
    (r : Fin d.fieldCount) :
    tsupport (projectionDerivativeCutoff d L a ab cd r) ⊆ tsupport (L.scalarCutoff a) :=
  cutoffCoefficient_support d L a _ _ _ _


theorem localization_projectionLowerSource_eq (ab : d.ProbeIndex) (z : d.Form) :
    L.localizationL2 a (d.lowerSource ab z) =
      (∑ cd : d.ProbeIndex, cutoffPullback d L a (projectionValueCutoff d L a ab cd)
        (d.valueCoefficient cd (d.inclusion z))) +
      ∑ cd : d.ProbeIndex, ∑ r : Fin d.fieldCount,
        cutoffPullback d L a (projectionDerivativeCutoff d L a ab cd r)
          (d.derivativeCoefficient r cd z) := by
  let V (cd : d.ProbeIndex) (w : d.Form) :=
    cutoffPullback d L a (projectionValueCutoff d L a ab cd)
      (d.valueCoefficient cd (d.inclusion w))
  let D (cd : d.ProbeIndex) (r : Fin d.fieldCount) (w : d.Form) :=
    cutoffPullback d L a (projectionDerivativeCutoff d L a ab cd r)
      (d.derivativeCoefficient r cd w)
  have heq : (fun w : d.Form => L.localizationL2 a (d.lowerSource ab w)) =
      fun w => (∑ cd, V cd w) + ∑ cd, ∑ r, D cd r w := by
    apply (intoFirstOrderGraph_denseRange d.fields d.charts.measure).equalizer
      ((L.localizationL2 a).continuous.comp (d.lowerSource ab).continuous)
    · apply Continuous.add
      · apply continuous_finset_sum
        intro cd _
        exact (cutoffPullback d L a _).continuous.comp
          ((d.valueCoefficient cd).continuous.comp d.inclusion.continuous)
      · apply continuous_finset_sum
        intro cd _
        apply continuous_finset_sum
        intro r _
        exact (cutoffPullback d L a _).continuous.comp (d.derivativeCoefficient r cd).continuous
    funext h
    let w := intoFirstOrderGraph d.fields d.charts.measure h
    let p : M → ℝ := fun x => projectionLowerSource d.fields d.charts g x
      (probes d.fields h x) (derivativeProbes d.fields h x) ab
    have hp : MemLp p 2 d.charts.measure :=
      (Lp.memLp (d.lowerSource ab w)).ae_eq (d.lowerSource_into_coe ab h)
    have hpEq : d.lowerSource ab w = hp.toLp p := by
      apply Lp.ext
      exact (d.lowerSource_into_coe ab h).trans hp.coeFn_toLp.symm
    have hloc := L.localizationL2_toLp_coe a hp
    rw [← hpEq] at hloc
    have hV (cd : d.ProbeIndex) : V cd w =ᵐ[volume] fun x =>
        projectionValueCutoff d L a ab cd x * scalarProbe d.fields h cd ((L.chart a).symm x) :=
      cutoffPullback_value_into_coe d L a _ (projectionValueCutoff_support d L a ab cd) cd h
    have hD (cd : d.ProbeIndex) (r : Fin d.fieldCount) : D cd r w =ᵐ[volume] fun x =>
        projectionDerivativeCutoff d L a ab cd r x *
          scalarDirectional (d.fields r) (scalarProbe d.fields h cd) ((L.chart a).symm x) :=
      cutoffPullback_derivative_into_coe d L a _
        (projectionDerivativeCutoff_support d L a ab cd r) r cd h
    change L.localizationL2 a (d.lowerSource ab w) =
      (∑ cd, V cd w) + ∑ cd, ∑ r, D cd r w
    apply Lp.ext
    filter_upwards [hloc, ae_all_iff.mpr hV,
      ae_all_iff.mpr (fun cd => ae_all_iff.mpr (hD cd)),
      Lp.coeFn_add (∑ cd, V cd w) (∑ cd, ∑ r, D cd r w),
      Lp.coeFn_fun_finsetSum Finset.univ (fun cd => V cd w),
      Lp.coeFn_fun_finsetSum Finset.univ (fun cd => ∑ r, D cd r w),
      ae_all_iff.mpr (fun cd => Lp.coeFn_fun_finsetSum Finset.univ (fun r => D cd r w))]
      with x hleft hvalue hderivative hadd hsumV hsumD hsumR
    rw [hleft, hadd, Pi.add_apply, hsumV, hsumD]
    simp_rw [hsumR, hvalue, hderivative]
    dsimp only [p, projectionValueCutoff, projectionDerivativeCutoff,
      cutoffCoefficient_apply, Function.comp_apply, projectionLowerSource]
    have hprobe (cd : d.ProbeIndex) :
        (probes d.fields h ((L.chart a).symm x)).ofLp cd =
          scalarProbe d.fields h cd ((L.chart a).symm x) := rfl
    have hderivativeProbe (r : Fin d.fieldCount) (cd : d.ProbeIndex) :
        (derivativeProbes d.fields h ((L.chart a).symm x)).ofLp (r, cd) =
          scalarDirectional (d.fields r) (scalarProbe d.fields h cd)
            ((L.chart a).symm x) := rfl
    simp only [hprobe, hderivativeProbe, mul_sub, mul_add, Finset.mul_sum,
      mul_assoc, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
    simp only [mul_assoc, mul_left_comm, mul_comm]
  exact congrFun heq z


theorem lowerSource_eq_nested_jet
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1)
    (hone : ∀ x ∈ tsupport (L.scalarCutoff a), L'.scalarCutoff b x = 1)
    (ab : d.ProbeIndex) (z : d.Form) :
    lowerSource d L a ab z =
      ((∑ cd : d.ProbeIndex, schwartzMultiplier (projectionValueCutoff d L a ab cd)
          (d.localizedValue L' b cd z)) +
        ∑ cd : d.ProbeIndex, ∑ r : Fin d.fieldCount, ∑ j : Fin n,
          schwartzMultiplier (cutoffCoefficient d L a
            (projectionDerivativeCutoff d L a ab cd r)
            (projectionDerivativeCutoff_support d L a ab cd r)
            (fun x => chartField a.val.1.val (d.fields r) x j)
            (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j))
            (d.localizedDerivative L' b cd j z)) +
      schwartzMultiplier (zeroOrderCutoff d L a) (d.localizedValue L' b ab z) +
      ∑ r : Fin d.fieldCount, ∑ j : Fin n,
        schwartzMultiplier (cutoffCoefficient d L a (firstOrderCutoff d L a r)
          (firstOrderCutoff_support d L a r)
          (fun x => chartField a.val.1.val (d.fields r) x j)
          (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j))
          (d.localizedDerivative L' b ab j z) := by
  simp only [NativeLocalizedEllipticEquationNative.lowerSource,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  rw [localization_projectionLowerSource_eq]
  simp_rw [cutoffPullback_value_eq d L a L' b hcenter _
    (projectionValueCutoff_support d L a ab _) (fun x hx => hone x
      (projectionValueCutoff_support d L a ab _ hx)),
    cutoffPullback_derivative_eq d L a L' b hcenter _
      (projectionDerivativeCutoff_support d L a ab _ _)
      (fun x hx => hone x (projectionDerivativeCutoff_support d L a ab _ _ hx))]
  rw [cutoffPullback_value_eq d L a L' b hcenter _ (zeroOrderCutoff_support d L a)
    (fun x hx => hone x (zeroOrderCutoff_support d L a hx))]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact cutoffPullback_derivative_eq d L a L' b hcenter _
    (firstOrderCutoff_support d L a r)
    (fun x hx => hone x (firstOrderCutoff_support d L a r hx)) r ab z


abbrev SourceIndex :=
  d.ProbeIndex ⊕ (d.ProbeIndex × Fin d.fieldCount × Fin n) ⊕
    Unit ⊕ (Fin d.fieldCount × Fin n) ⊕ (Fin n × Fin n)

def sourceExpression (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex) :
    SourceIndex d → JetExpression n
  | .inl cd => .term (projectionValueCutoff d L a ab cd) []
  | .inr (.inl (cd, r, j)) => .term
      (cutoffCoefficient d L a (projectionDerivativeCutoff d L a ab cd r)
        (projectionDerivativeCutoff_support d L a ab cd r)
        (fun x => chartField a.val.1.val (d.fields r) x j)
        (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j)) [j]
  | .inr (.inr (.inl _)) => .term (zeroOrderCutoff d L a) []
  | .inr (.inr (.inr (.inl (r, j)))) => .term
      (cutoffCoefficient d L a (firstOrderCutoff d L a r)
        (firstOrderCutoff_support d L a r)
        (fun x => chartField a.val.1.val (d.fields r) x j)
        (contDiffOn_chartField_coordinate a.val.1.val (d.fields r) j)) [j]
  | .inr (.inr (.inr (.inr (i, j)))) =>
      .term (-(∂_{EuclideanSpace.single j (1 : ℝ)} (A i j))) [i]

theorem sourceExpression_order (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (c : SourceIndex d) : (sourceExpression d L a A ab c).orderLE 1 := by
  rcases c with cd | (cd | (c | (r | ij))) <;>
    simp only [sourceExpression, JetExpression.orderLE, List.length_nil,
      List.length_cons] <;> omega


def sourceSolutionJet (ab : d.ProbeIndex)
    (Q : d.ProbeIndex → List (Fin n) → ScalarL2 n)
    (q : List (Fin n) → ScalarL2 n) : SourceIndex d → List (Fin n) → ScalarL2 n
  | .inl cd => Q cd
  | .inr (.inl (cd, _, _)) => Q cd
  | .inr (.inr (.inl _)) => Q ab
  | .inr (.inr (.inr (.inl _))) => Q ab
  | .inr (.inr (.inr (.inr _))) => q

def divergenceSourceJet (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (B : List (Fin n) → ScalarL2 n)
    (Q : d.ProbeIndex → List (Fin n) → ScalarL2 n)
    (q : List (Fin n) → ScalarL2 n) : List (Fin n) → ScalarL2 n :=
  finiteSourceJet B (sourceSolutionJet d ab Q q) (sourceExpression d L a A ab)

theorem isWeakSchwartzJet_divergenceSourceJet
    (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (B : List (Fin n) → ScalarL2 n)
    (Q : d.ProbeIndex → List (Fin n) → ScalarL2 n)
    (q : List (Fin n) → ScalarL2 n) {s : ℕ}
    (hB : IsWeakSchwartzJet B s)
    (hQ : ∀ cd, IsWeakSchwartzJet (Q cd) (s + 1))
    (hq : IsWeakSchwartzJet q (s + 1)) :
    IsWeakSchwartzJet (divergenceSourceJet d L a A ab B Q q) s := by
  apply isWeakSchwartzJet_finiteSourceJet _ _ _ hB _
    (sourceExpression_order d L a A ab)
  intro c
  rcases c with cd | (cd | (c | (r | ij)))
  · exact hQ cd
  · exact hQ cd.1
  · exact hQ ab
  · exact hQ ab
  · exact hq


theorem divergenceSourceJet_nil
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1)
    (hone : ∀ x ∈ tsupport (L.scalarCutoff a), L'.scalarCutoff b x = 1)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (v : d.Value) (z : d.Form)
    (B : List (Fin n) → ScalarL2 n)
    (Q : d.ProbeIndex → List (Fin n) → ScalarL2 n)
    (q : List (Fin n) → ScalarL2 n)
    (hB : B [] = L.localizationL2 a (d.valueCoefficient ab v))
    (hQ0 : ∀ cd, Q cd [] = d.localizedValue L' b cd z)
    (hQ1 : ∀ cd j, Q cd [j] = d.localizedDerivative L' b cd j z)
    (hq1 : ∀ i, q [i] = d.localizedDerivative L a ab i z) :
    divergenceSourceJet d L a A ab B Q q [] =
      DeTurckLocalizedH2Native.divergenceSource d L a A ab v z := by
  have hneg (θ : 𝓢(E, ℝ)) (f : ScalarL2 n) :
      schwartzMultiplier (-θ) f = -(schwartzMultiplier θ f) := by
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (-θ) f, schwartzMultiplier_coe θ f,
      Lp.coeFn_neg (schwartzMultiplier θ f)] with x hn hp hm
    rw [hn, hm, Pi.neg_apply, hp]
    simp only [SchwartzMap.neg_apply, neg_mul]
  rw [divergenceSourceJet, finiteSourceJet_nil,
    DeTurckLocalizedH2Native.divergenceSource,
    lowerSource_eq_nested_jet d L a L' b hcenter hone]
  simp only [SourceIndex, Fintype.sum_sum_type, Fintype.sum_prod_type,
    sourceExpression, sourceSolutionJet, JetExpression.eval, Fintype.sum_unique,
    hB, hQ0, hQ1, hq1, hneg, Finset.sum_neg_distrib]
  abel

theorem localizedValue_weakDerivative (ab : d.ProbeIndex) (z : d.Form) (i : Fin n) :
    HasWeakSchwartzDerivative (d.localizedValue L a ab z)
      (d.localizedDerivative L a ab i z) (EuclideanSpace.single i (1 : ℝ)) := by
  intro φ
  have h := localizedDerivative_pairing d L a ab z i φ
  simp only [PiLp.basisFun_apply] at h
  linarith


theorem weakJet_singleton_eq_localizedDerivative
    (ab : d.ProbeIndex) (z : d.Form) (q : List (Fin n) → ScalarL2 n) {s : ℕ}
    (hq : IsWeakSchwartzJet q (s + 1))
    (hzero : q [] = d.localizedValue L a ab z) (i : Fin n) :
    q [i] = d.localizedDerivative L a ab i z := by
  have h := hq [] (by simp) i
  rw [hzero] at h
  exact h.unique (localizedValue_weakDerivative d L a ab z i)

theorem localizedValue_ae_support (ab : d.ProbeIndex) (z : d.Form) :
    ∀ᵐ x ∂volume, x ∉ tsupport (L.scalarCutoff a) → d.localizedValue L a ab z x = 0 := by
  filter_upwards [L.localizationL2_coe a (d.valueCoefficient ab (d.inclusion z))]
    with x hx hnot
  change L.localizationL2 a (d.valueCoefficient ab (d.inclusion z)) x = 0
  rw [hx, image_eq_zero_of_notMem_tsupport hnot, zero_mul]


theorem divergenceSourceJet_nil_of_weak
    (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
    (hcenter : b.val.1 = a.val.1)
    (hone : ∀ x ∈ tsupport (L.scalarCutoff a), L'.scalarCutoff b x = 1)
    (A : Fin n → Fin n → 𝓢(E, ℝ)) (ab : d.ProbeIndex)
    (v : d.Value) (z : d.Form)
    (B : List (Fin n) → ScalarL2 n)
    (Q : d.ProbeIndex → List (Fin n) → ScalarL2 n)
    (q : List (Fin n) → ScalarL2 n) {s : ℕ}
    (hB : B [] = L.localizationL2 a (d.valueCoefficient ab v))
    (hQ0 : ∀ cd, Q cd [] = d.localizedValue L' b cd z)
    (hQ : ∀ cd, IsWeakSchwartzJet (Q cd) (s + 1))
    (hq0 : q [] = d.localizedValue L a ab z)
    (hq : IsWeakSchwartzJet q (s + 1)) :
    divergenceSourceJet d L a A ab B Q q [] =
      DeTurckLocalizedH2Native.divergenceSource d L a A ab v z :=
  divergenceSourceJet_nil d L a L' b hcenter hone A ab v z B Q q hB hQ0
    (fun cd => weakJet_singleton_eq_localizedDerivative d L' b cd z (Q cd)
      (hQ cd) (hQ0 cd))
    (weakJet_singleton_eq_localizedDerivative d L a ab z q hq hq0)



theorem generatorGraph_extend_localizedJet
    (ab : d.ProbeIndex) (z : d.Form) (v : d.Value)
    (hgen : d.GeneratorGraph (d.inclusion z) v) (s : ℕ)
    (hlow : ∀ (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
      (cd : d.ProbeIndex), ∃ q : List (Fin n) → ScalarL2 n,
        q [] = d.localizedValue L' b cd z ∧ IsWeakSchwartzJet q (s + 1))
    (himage : ∃ B : List (Fin n) → ScalarL2 n,
      B [] = L.localizationL2 a (d.valueCoefficient ab v) ∧ IsWeakSchwartzJet B s) :
    ∃ q : List (Fin n) → ScalarL2 n,
      q [] = d.localizedValue L a ab z ∧ IsWeakSchwartzJet q (s + 2) := by
  classical
  obtain ⟨L', b, hcenter, hone⟩ := exists_nested_localization d L a
  choose Q hQ0 hQ using hlow L' b
  obtain ⟨q, hq0, hq⟩ := hlow L a ab
  obtain ⟨B, hB0, hB⟩ := himage
  obtain ⟨r, hr, h2U, ell, hEll, A, hA, hell⟩ :=
    DeTurckLocalizedH2Native.exists_principal_coefficient_extensions d L a
  obtain ⟨C, hC, hAC⟩ :=
    DeTurckGeneratorRegularityNative.exists_schwartz_matrix_derivative_bound A
  obtain ⟨z', hz', _, heq⟩ :=
    DeTurckLocalizedH2Native.generatorGraph_extended_divergence_equation d L a
      hr h2U A hA hgen
  have hzz : z' = z := d.inclusion_injective hz'
  subst z'
  let G := divergenceSourceJet d L a A ab B Q q
  have hG : IsWeakSchwartzJet G s :=
    isWeakSchwartzJet_divergenceSourceJet d L a A ab B Q q hB hQ hq
  have hG0 : G [] = DeTurckLocalizedH2Native.divergenceSource d L a A ab v z :=
    divergenceSourceJet_nil_of_weak d L a L' b hcenter hone A ab v z
      B Q q hB0 hQ0 hQ hq0 hq
  have hq1 (i : Fin n) : q [i] = d.localizedDerivative L a ab i z :=
    weakJet_singleton_eq_localizedDerivative d L a ab z q hq hq0 i
  have hD (i : Fin n) : HasWeakSchwartzDerivative (q []) (q [i])
      (EuclideanSpace.single i (1 : ℝ)) := hq [] (by simp) i
  have hsupport : ∀ᵐ x ∂volume, x ∉ tsupport (L.scalarCutoff a) → q [] x = 0 := by
    rw [hq0]
    exact localizedValue_ae_support d L a ab z
  have hregion : cthickening (3 * (r / 2)) (tsupport (L.scalarCutoff a)) ⊆
      cthickening (r + r) (tsupport (L.scalarCutoff a)) :=
    cthickening_mono (by linarith) _
  have hdiv : DivergenceEquation A (fun i => q [i]) (G [])
      (cthickening (3 * (r / 2)) (tsupport (L.scalarCutoff a))) := by
    intro φ hφ hφK
    simp_rw [hq1, hG0]
    exact heq ab φ hφ (hφK.trans hregion)
  obtain ⟨q', hq'0, _, hq', _⟩ := exists_finite_weakJet_of_divergence
    (q []) (fun i => q [i]) hD (cutoff_compactSupport d L a) hsupport A
    (by positivity : 0 < r / 2) hEll hC
    (fun x hx => hell x (hregion hx)) hAC G hdiv s hG
  exact ⟨q', hq'0.trans hq0, hq'⟩

theorem symmetricScaleValue_add (k l : ℕ) (x : SpectralHeatNative.State d.SymmetricIndex) :
    d.symmetricScaleValue (k + l) x =
      d.symmetricScaleValue k (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  change d.symmetricBasis.repr.symm (SpectralHeatNative.scaleDecode d.symmetricParameters
    (k + l) x) = d.symmetricBasis.repr.symm (SpectralHeatNative.scaleDecode
      d.symmetricParameters k (SpectralHeatNative.scaleDecode d.symmetricParameters l x))
  rw [SpectralHeatNative.scaleDecode_add]
  rfl

theorem exists_symmetricScale_form (k : ℕ) (x : SpectralHeatNative.State d.SymmetricIndex) :
    ∃ z : d.Form, d.inclusion z = (d.symmetricScaleValue (k + 1) x : d.Value) := by
  let B : HilbertBasis d.SymmetricIndex ℝ d.SymmetricForm := by
    apply HilbertResolventNative.formEigenbasis
      (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
    · exact d.symmetricInclusion_compact
    · exact d.symmetricInclusion_denseRange
    · exact d.symmetricInclusion_injective
  let z : d.SymmetricForm :=
    B.repr.symm (SpectralHeatNative.scaleDecode d.symmetricParameters k x)
  have h : d.symmetricScaleValue (k + 1) x = d.symmetricInclusion z := by
    calc
      d.symmetricScaleValue (k + 1) x =
          d.symmetricScaleValue 1 (SpectralHeatNative.scaleDecode d.symmetricParameters k x) := by
        simpa only [Nat.add_comm k 1] using symmetricScaleValue_add d 1 k x
      _ = d.symmetricInclusion z := by
        apply HilbertResolventNative.scaleValue_one
          (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
        all_goals first
          | exact d.symmetricInclusion_compact
          | exact d.symmetricInclusion_denseRange
          | exact d.symmetricInclusion_injective
          | exact d.norm_symmetricInclusion_le_one
  exact ⟨(z : d.Form), (congrArg (fun v : d.SymmetricValue => (v : d.Value)) h).symm⟩

theorem symmetricScale_generatorGraph (k : ℕ)
    (x : SpectralHeatNative.State d.SymmetricIndex) :
    d.GeneratorGraph (d.symmetricScaleValue (k + 2) x : d.Value)
      ((d.symmetricScaleValue k x : d.Value) - (d.symmetricScaleValue (k + 2) x : d.Value)) := by
  have h : d.symmetricScaleValue (k + 2) x =
      d.symmetricResolvent (d.symmetricScaleValue k x) := by
    rw [Nat.add_comm k 2, symmetricScaleValue_add]
    apply HilbertResolventNative.scaleValue_two
      (V := ↥d.symmetricForm) (H := ↥d.symmetricValue) d.symmetricInclusion
    all_goals first
      | exact d.symmetricInclusion_compact
      | exact d.symmetricInclusion_denseRange
      | exact d.norm_symmetricInclusion_le_one
  have hs : d.SymmetricGeneratorGraph (d.symmetricScaleValue (k + 2) x)
      (d.symmetricScaleValue k x - d.symmetricScaleValue (k + 2) x) := by
    change d.symmetricResolvent (d.symmetricScaleValue (k + 2) x +
      (d.symmetricScaleValue k x - d.symmetricScaleValue (k + 2) x)) = _
    rw [show d.symmetricScaleValue (k + 2) x +
      (d.symmetricScaleValue k x - d.symmetricScaleValue (k + 2) x) =
        d.symmetricScaleValue k x by abel]
    exact h.symm
  exact (d.symmetricGeneratorGraph_iff (d.symmetricScaleValue (k + 2) x)
    (d.symmetricScaleValue k x - d.symmetricScaleValue (k + 2) x)).mp hs


theorem exists_symmetricScale_localized_weakJet (k : ℕ) :
    ∀ (L : FiniteChartLocalizationData d.charts) (a : L.patches) (ab : d.ProbeIndex)
      (x : SpectralHeatNative.State d.SymmetricIndex),
      ∃ q : List (Fin n) → ScalarL2 n,
        q [] = L.localizationL2 a
          (d.valueCoefficient ab (d.symmetricScaleValue k x : d.Value)) ∧
          IsWeakSchwartzJet q k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    intro L a ab x
    refine ⟨fun _ => L.localizationL2 a
      (d.valueCoefficient ab (d.symmetricScaleValue 0 x : d.Value)), rfl, ?_⟩
    intro w hw
    omega
  | one =>
    intro L a ab x
    obtain ⟨z, hz⟩ := exists_symmetricScale_form d 0 x
    let q : List (Fin n) → ScalarL2 n
      | [] => d.localizedValue L a ab z
      | i :: _ => d.localizedDerivative L a ab i z
    refine ⟨q, ?_, ?_⟩
    · change L.localizationL2 a (d.valueCoefficient ab (d.inclusion z)) = _
      rw [hz]
    · intro w hw i
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst w
      exact localizedValue_weakDerivative d L a ab z i
  | more k ih ih1 =>
    intro L a ab x
    obtain ⟨z, hz⟩ := exists_symmetricScale_form d (k + 1) x
    have hstep : d.symmetricScaleValue (k + 1)
        (SpectralHeatNative.scaleDecode d.symmetricParameters 1 x) =
        d.symmetricScaleValue (k + 2) x :=
      (symmetricScaleValue_add d (k + 1) 1 x).symm
    have hlow (L' : FiniteChartLocalizationData d.charts) (b : L'.patches)
        (cd : d.ProbeIndex) : ∃ q : List (Fin n) → ScalarL2 n,
          q [] = d.localizedValue L' b cd z ∧ IsWeakSchwartzJet q (k + 1) := by
      obtain ⟨q, hq0, hq⟩ := ih1 L' b cd (SpectralHeatNative.scaleDecode d.symmetricParameters 1 x)
      refine ⟨q, ?_, hq⟩
      change q [] = L'.localizationL2 b (d.valueCoefficient cd (d.inclusion z))
      rw [hz]
      simpa only [hstep] using hq0
    let v : d.Value := (d.symmetricScaleValue k x : d.Value) -
      (d.symmetricScaleValue (k + 2) x : d.Value)
    have hgen : d.GeneratorGraph (d.inclusion z) v := by
      rw [hz]
      exact symmetricScale_generatorGraph d k x
    obtain ⟨R, hR0, hR⟩ := ih L a ab x
    obtain ⟨q, hq0, hq⟩ := hlow L a ab
    have himage : ∃ B : List (Fin n) → ScalarL2 n,
        B [] = L.localizationL2 a (d.valueCoefficient ab v) ∧ IsWeakSchwartzJet B k := by
      refine ⟨fun w => R w - q w, ?_, hR.sub (hq.mono (by omega))⟩
      change R [] - q [] = _
      rw [hR0, hq0]
      change L.localizationL2 a (d.valueCoefficient ab (d.symmetricScaleValue k x : d.Value)) -
        L.localizationL2 a (d.valueCoefficient ab (d.inclusion z)) = _
      rw [hz]
      simp only [v, map_sub]
    obtain ⟨q', hq'0, hq'⟩ := generatorGraph_extend_localizedJet d L a ab z v hgen k hlow himage
    refine ⟨q', ?_, hq'⟩
    change q' [] = L.localizationL2 a
      (d.valueCoefficient ab (d.symmetricScaleValue (k + 2) x : d.Value))
    rw [← hz]
    exact hq'0


theorem exists_symmetricScale_localized_weakJet_bound (k : ℕ) (ab : d.ProbeIndex) :
    ∃ C : ℝ, 0 < C ∧
      ∃ q : SpectralHeatNative.State d.SymmetricIndex → List (Fin n) → ScalarL2 n,
        (∀ x, q x [] = L.localizationL2 a
          (d.valueCoefficient ab (d.symmetricScaleValue k x : d.Value))) ∧
        (∀ x, IsWeakSchwartzJet (q x) k) ∧
        ∀ x w, w.length ≤ k → ‖q x w‖ ≤ C * ‖x‖ := by
  classical
  choose q hq0 hq using exists_symmetricScale_localized_weakJet d k L a ab
  let U : SpectralHeatNative.State d.SymmetricIndex →L[ℝ] ScalarL2 n :=
    (L.localizationL2 a).comp ((d.valueCoefficient ab).comp
      (d.symmetricValue.subtypeL.comp (d.symmetricScaleValue k)))
  obtain ⟨C, hC, hbound⟩ := DeTurckDomainRegularityNative.exists_finite_weakJet_bound
    U q k hq0 hq
  exact ⟨C, hC, q, hq0, hq, hbound⟩

def localizedScaleValue (ab : d.ProbeIndex) (k : ℕ) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] ScalarL2 n :=
  (L.localizationL2 a).comp ((d.valueCoefficient ab).comp
    (d.symmetricValue.subtypeL.comp (d.symmetricScaleValue k)))

theorem exists_localizedScaleDerivative (ab : d.ProbeIndex) (k : ℕ)
    (w : List (Fin n)) (hw : w.length ≤ k) :
    ∃ D : SpectralHeatNative.State d.SymmetricIndex →L[ℝ] ScalarL2 n,
      ∀ x (φ : 𝓢(E, ℝ)), inner ℝ (D x) (φ.toLp 2 volume) =
        (-1 : ℝ) ^ w.length * inner ℝ (localizedScaleValue d L a ab k x)
          ((DeTurckDomainRegularityNative.orderedSchwartzDerivative w.reverse φ).toLp 2 volume) := by
  apply DeTurckDomainRegularityNative.exists_continuous_weakJet
    (localizedScaleValue d L a ab k) w
  intro x
  obtain ⟨q, hq0, hq⟩ := exists_symmetricScale_localized_weakJet d k L a ab x
  refine ⟨q w, ?_⟩
  intro φ
  have hzero : q [] = localizedScaleValue d L a ab k x := by
    change q [] = L.localizationL2 a
      (d.valueCoefficient ab (d.symmetricScaleValue k x : d.Value))
    exact hq0
  simpa only [hzero] using DeTurckDomainRegularityNative.finite_weakJet_pairing q k hq w hw φ


def localizedScaleDerivative (ab : d.ProbeIndex) (k : ℕ)
    (w : List (Fin n)) (hw : w.length ≤ k) :
    SpectralHeatNative.State d.SymmetricIndex →L[ℝ] ScalarL2 n :=
  (exists_localizedScaleDerivative d L a ab k w hw).choose

theorem localizedScaleDerivative_pairing (ab : d.ProbeIndex) (k : ℕ)
    (w : List (Fin n)) (hw : w.length ≤ k)
    (x : SpectralHeatNative.State d.SymmetricIndex) (φ : 𝓢(E, ℝ)) :
    inner ℝ (localizedScaleDerivative d L a ab k w hw x) (φ.toLp 2 volume) =
      (-1 : ℝ) ^ w.length * inner ℝ (localizedScaleValue d L a ab k x)
        ((DeTurckDomainRegularityNative.orderedSchwartzDerivative w.reverse φ).toLp 2 volume) :=
  (exists_localizedScaleDerivative d L a ab k w hw).choose_spec x φ

theorem localizedScaleDerivative_eq_jet (ab : d.ProbeIndex) (k : ℕ)
    (w : List (Fin n)) (hw : w.length ≤ k)
    (x : SpectralHeatNative.State d.SymmetricIndex) (q : List (Fin n) → ScalarL2 n)
    (hq0 : q [] = localizedScaleValue d L a ab k x) (hq : IsWeakSchwartzJet q k) :
    localizedScaleDerivative d L a ab k w hw x = q w := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
    (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
  intro φ
  simp only [SchwartzMap.toLpCLM_apply]
  rw [localizedScaleDerivative_pairing,
    DeTurckDomainRegularityNative.finite_weakJet_pairing q k hq w hw φ, hq0]

theorem localizedScaleDerivative_nil (ab : d.ProbeIndex) (k : ℕ) :
    localizedScaleDerivative d L a ab k [] (by simp) = localizedScaleValue d L a ab k := by
  apply ContinuousLinearMap.ext
  intro x
  apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
    (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
  intro φ
  simp only [SchwartzMap.toLpCLM_apply, localizedScaleDerivative_pairing,
    List.length_nil, pow_zero, List.reverse_nil,
    DeTurckDomainRegularityNative.orderedSchwartzDerivative, one_mul]


theorem localizedScaleDerivative_scaleDecode (ab : d.ProbeIndex) (k l : ℕ)
    (w : List (Fin n)) (hw : w.length ≤ k)
    (x : SpectralHeatNative.State d.SymmetricIndex) :
    localizedScaleDerivative d L a ab (k + l) w (by omega) x =
      localizedScaleDerivative d L a ab k w hw
        (SpectralHeatNative.scaleDecode d.symmetricParameters l x) := by
  apply (SchwartzMap.denseRange_toLpCLM (F := ℝ)
    (μ := (volume : Measure E)) (by norm_num : (2 : ENNReal) ≠ ⊤)).eq_of_inner_left ℝ
  intro φ
  simp only [SchwartzMap.toLpCLM_apply]
  rw [localizedScaleDerivative_pairing, localizedScaleDerivative_pairing]
  congr 2
  change L.localizationL2 a (d.valueCoefficient ab (d.symmetricScaleValue (k + l) x : d.Value)) =
    L.localizationL2 a (d.valueCoefficient ab (d.symmetricScaleValue k
      (SpectralHeatNative.scaleDecode d.symmetricParameters l x) : d.Value))
  rw [symmetricScaleValue_add]

end PoincareConjecture.DeTurckNestedLocalizationNative

end
