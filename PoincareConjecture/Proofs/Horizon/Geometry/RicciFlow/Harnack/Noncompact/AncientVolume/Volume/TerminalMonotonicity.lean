import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem edist_le_mul_of_global_tangentNorm_le
    (g h : RiemannianMetric n M) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x),
      h.tangentNorm x v ≤ C * g.tangentNorm x v)
    (x y : M) : h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiv : h.edist x y / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hr
    have hlength := pathELength_le_of_tangentNorm_le g h γ 0 1 C hC.le
      (fun _ _ => hbound _)
    have hdist : h.edist x y ≤ h.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγsmooth hγ0 hγ1 zero_le_one
    apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hC)
      ENNReal.ofReal_ne_top).mpr
    exact (hdist.trans hlength).trans (by
      rw [mul_comm r]
      exact mul_le_mul_right hγlength.le _)
  simpa only [mul_comm] using
    (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hC)
      ENNReal.ofReal_ne_top).mp hdiv

private theorem volumeMeasure_le_of_global_tangentNorm_le
    (g h : RiemannianMetric n M) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x),
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (s : Set M) :
    h.volumeMeasure s ≤ ENNReal.ofReal C ^ n * g.volumeMeasure s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₁ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₂ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hcoe : (Cn : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq Cn
  have hLip : @LipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace
      Cn id := by
    intro x y
    change h.edist x y ≤ (Cn : ℝ≥0∞) * g.edist x y
    rw [hcoe]
    exact edist_le_mul_of_global_tangentNorm_le g h hC hbound x y
  have hraw := @LipschitzWith.hausdorffMeasure_image_le M M m₁ m₂
    inferInstance inferInstance inferInstance inferInstance (K := Cn) (f := id)
    hLip (d := (n : ℝ)) (by positivity) s
  simp only [Set.image_id, ENNReal.rpow_natCast, hcoe] at hraw
  change (Measure.euclideanHausdorffMeasure n) s ≤ _ *
    (@Measure.euclideanHausdorffMeasure M m₁ inferInstance inferInstance n) s
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact (mul_le_mul_right hraw _).trans_eq (by ac_rfl)




theorem asymptoticVolumeRatio_le_of_tangentNorm_bounds
    [SecondCountableTopology M]
    (g h : RiemannianMetric n M) (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (hn : 1 ≤ n) (hgc : MetricComplete g) (hhc : MetricComplete h)
    (hRg : ∀ x (v : TangentSpace (𝓡 n) x), 0 ≤ Dg.ricci x v v)
    (hRh : ∀ x (v : TangentSpace (𝓡 n) x), 0 ≤ Dh.ricci x v v)
    {C : ℝ} (hC : 0 < C)
    (hforward : ∀ x (v : TangentSpace (𝓡 n) x),
      h.tangentNorm x v ≤ C * g.tangentNorm x v)
    (hreverse : ∀ x (v : TangentSpace (𝓡 n) x),
      g.tangentNorm x v ≤ C * h.tangentNorm x v) (p : M) :
    h.asymptoticVolumeRatio p ≤ C ^ (2 * n) * g.asymptoticVolumeRatio p := by
  have hball (r : ℝ) : h.volumeMeasure (h.ball p r) ≤
      ENNReal.ofReal C ^ n * g.volumeMeasure (g.ball p (C * r)) :=
    (volumeMeasure_le_of_global_tangentNorm_le g h hC hforward _).trans
      (mul_le_mul_right (measure_mono
        (ball_subset_ball_of_tangentNorm_le h g p r C hC
          (fun x _ => hreverse x))) _)
  have hlim := (g.tendsto_asymptoticVolumeRatio Dg hn hgc hRg p).comp
    (Filter.Tendsto.const_mul_atTop hC tendsto_id)
  have hscaled : Tendsto (fun r : ℝ =>
      C ^ n * (g.volumeMeasure (g.ball p (C * r))).toReal / r ^ n)
      atTop (𝓝 (C ^ (2 * n) * g.asymptoticVolumeRatio p)) := by
    have haux := hlim.const_mul (C ^ (2 * n))
    apply haux.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Function.comp_apply, id_eq, mul_pow, pow_mul]
    field_simp
    ring
  apply le_of_tendsto_of_tendsto (h.tendsto_asymptoticVolumeRatio Dh hn hhc hRh p)
    hscaled
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le n)
  have hv := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (g.ball_volume_ne_top_of_metricComplete hgc p (C * r))) (hball r)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hC.le] using hv

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem asymptoticVolumeRatio_le_exp_of_bounded_ancient
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hn : 1 ≤ n) (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) (p : M) :
    (F.metric b).asymptoticVolumeRatio p ≤
      Real.exp ((n : ℝ) ^ 3 * K * |b - a|) ^ (2 * n) *
        (F.metric a).asymptoticVolumeRatio p := by
  have hRic (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 n) x) :
      |(F.connection t).ricci x v v| ≤
        ((n : ℝ) ^ 3 * K) * (F.metric t).inner x v v := by
    have hnorm := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    have hQ : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound t ht x) (by positivity)) hQ)
  apply RiemannianMetric.asymptoticVolumeRatio_le_of_tangentNorm_bounds
    (F.metric a) (F.metric b) (F.connection a) (F.connection b) hn
    (hcomplete a ha) (hcomplete b hb)
    (fun x v => ((F.connection a).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric a) (F.connection a)) x (hoperator a ha x) v).1)
    (fun x v => ((F.connection b).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric b) (F.connection b)) x (hoperator b hb x) v).1)
    (Real.exp_pos _) _ _ p
  · intro x v
    exact F.tangentNorm_le_exp_of_ricci_bound (convex_Iic 0) (Subset.refl _) x v
      ((n : ℝ) ^ 3 * K) (fun t ht => hRic t ht x v) ha hb
  · intro x v
    simpa only [abs_sub_comm a b] using
      F.tangentNorm_le_exp_of_ricci_bound (convex_Iic 0) (Subset.refl _) x v
        ((n : ℝ) ^ 3 * K) (fun t ht => hRic t ht x v) hb ha



theorem antitoneOn_asymptoticVolumeRatio_of_bounded_ancient
    {m : ℕ} {N : Type u} [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N] [T3Space N] [SecondCountableTopology N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N] [IsManifold (𝓡 (m + 1)) ∞ N]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) N (Iic 0))
    (hm : 0 < m) (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) (p : N) :
    AntitoneOn (fun t => (F.metric t).asymptoticVolumeRatio p) (Iic 0) := by
  have hinterior {a b : ℝ} (hab : a ≤ b) (hb : b < 0) :
      (F.metric b).asymptoticVolumeRatio p ≤ (F.metric a).asymptoticVolumeRatio p := by
    have hJ : Icc a b ⊆ interior (Iic (0 : ℝ)) := by
      rw [interior_Iic]
      exact fun t ht => ht.2.trans_lt hb
    have hspec := F.asymptoticVolumeRatio_spec hC hm hJ
      (fun t ht => hcomplete t (ht.2.trans hb.le))
      (fun t ht => hoperator t (ht.2.trans hb.le))
      (mul_nonneg (sq_nonneg ((m + 1 : ℕ) : ℝ)) hK)
      (fun t ht x => (le_abs_self _).trans
        (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
          (mul_le_mul_of_nonneg_left (hbound t (ht.2.trans hb.le) x)
            (sq_nonneg _)))) p
    exact hspec.2 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  intro a ha b hb hab
  change a ≤ 0 at ha
  change b ≤ 0 at hb
  rcases lt_or_eq_of_le hb with hbneg | rfl
  · exact hinterior hab hbneg
  rcases lt_or_eq_of_le hab with haneg | rfl
  · have hlimit : Tendsto (fun t : ℝ =>
        Real.exp (((m + 1 : ℕ) : ℝ) ^ 3 * K * |0 - t|) ^ (2 * (m + 1)) *
          (F.metric a).asymptoticVolumeRatio p)
        (𝓝[<] 0) (𝓝 ((F.metric a).asymptoticVolumeRatio p)) := by
      have hc : Continuous (fun t : ℝ =>
          Real.exp (((m + 1 : ℕ) : ℝ) ^ 3 * K * |0 - t|) ^ (2 * (m + 1)) *
            (F.metric a).asymptoticVolumeRatio p) := by fun_prop
      simpa using (hc.tendsto 0).mono_left
        (show 𝓝[<] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds haneg)] with t ht hat
    have hcompare := F.asymptoticVolumeRatio_le_exp_of_bounded_ancient
      hC (by omega) hcomplete hoperator hbound ht.le le_rfl p
    exact hcompare.trans (mul_le_mul_of_nonneg_left (hinterior hat.le ht) (by positivity))
  · exact le_rfl

end PoincareConjecture.RicciFlow
