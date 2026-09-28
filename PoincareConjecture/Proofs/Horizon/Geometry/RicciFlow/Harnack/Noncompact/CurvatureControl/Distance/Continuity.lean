import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.DirectionEvaluation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem continuousAt_ricci_tangent_evaluation
    (F : RicciFlow n M J) (hTensor : ∀ t, (F.connection t).CurvatureTensorCalculus)
    (q : ℝ × TangentBundle (𝓡 n) M) (hq : q.1 ∈ interior J) :
    ContinuousAt (fun z : ℝ × TangentBundle (𝓡 n) M =>
      (F.connection z.1).ricci z.2.1 z.2.2 z.2.2) q := by
  apply Poincare.RicciFlow.Harnack.continuousAt_tensor_family_evaluation
    (q := q) (t := Prod.fst) (x := fun z => z.2.1)
    (T := fun t => (F.connection t).ricciEvaluation)
    (fun t => (hTensor t).2.1)
    (X := fun z (_ : Fin 2) => z.2.2)
  · intro O hO hx X hX
    exact (F.contMDiffAt_ricci_fields hq
      ((hX 0).contMDiffAt (hO.mem_nhds hx))
      ((hX 1).contMDiffAt (hO.mem_nhds hx))).continuousAt
  · exact continuousAt_fst
  · exact (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n))).continuousAt.comp continuousAt_snd
  · intro i
    exact continuousAt_snd

private theorem exists_ricci_bound_on_compact_relative
    [T3Space M] (F : RicciFlow n M J)
    (hTensor : ∀ t, (F.connection t).CurvatureTensorCalculus)
    (g : RiemannianMetric n M) {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ∀ v : TangentSpace (𝓡 n) x,
        |(F.connection t).ricci x v v| ≤ C * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let S : Set (TangentBundle (𝓡 n) M) := {q | q.1 ∈ K ∧ ‖q.2‖ = 1}
  have hS : IsCompact S := Poincare.VectorBundle.isCompact_sphere_over hK 1
  have hcont : ContinuousOn (fun z : ℝ × TangentBundle (𝓡 n) M =>
      (F.connection z.1).ricci z.2.1 z.2.2 z.2.2) (Icc a b ×ˢ S) :=
    fun q hq => (continuousAt_ricci_tangent_evaluation F hTensor q (hJ hq.1)).continuousWithinAt
  obtain ⟨C, hCbound⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x hx v
  obtain ⟨R, hR⟩ := (hTensor t).2.1.1 x
  have hscale (c : ℝ) (w : TangentSpace (𝓡 n) x) :
      (F.connection t).ricci x (c • w) (c • w) =
        c ^ 2 * (F.connection t).ricci x w w := by
    have h := R.map_smul_univ (fun _ : Fin 2 => c) (fun _ => w)
    simp_rw [← hR] at h
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_two, pow_two] using h
  by_cases hv : v = 0
  · subst v
    have hz := hscale 0 (0 : TangentSpace (𝓡 n) x)
    simpa using hz
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, norm_inv, inv_mul_cancel₀ hn]
  have hbound := hCbound (t, ⟨x, w⟩) ⟨ht, hx, hw⟩
  have hbound' : |(F.connection t).ricci x w w| ≤ C := by
    simpa only [Real.norm_eq_abs] using hbound
  have hvw : v = ‖v‖ • w := by simp [w, smul_smul, mul_inv_cancel₀ hn]
  have hnorm : ‖v‖ ^ 2 = g.inner x v v := (real_inner_self_eq_norm_sq v).symm
  calc
    |(F.connection t).ricci x v v| =
        ‖v‖ ^ 2 * |(F.connection t).ricci x w w| := by
      conv_lhs => rw [hvw, hscale]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * max C 0 := mul_le_mul_of_nonneg_left
      (hbound'.trans (le_max_left C 0))
      (sq_nonneg _)
    _ = max C 0 * g.inner x v v := by rw [hnorm]; ring

private theorem exists_local_distance_exp_comparison
    [T3Space M] [PreconnectedSpace M]
    (F : RicciFlow n M J) (hTensor : ∀ t, (F.connection t).CurvatureTensorCalculus)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (hcomplete : MetricComplete (F.metric b))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (O : M) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ∀ y ∈ (F.metric a).ball O r,
        ((F.metric t).edist O y).toReal ≤ Real.exp (C * |t - s|) *
          ((F.metric s).edist O y).toReal := by
  obtain ⟨C, hCnonneg, hbound⟩ := exists_ricci_bound_on_compact_relative F hTensor
    (F.metric b) hJ
    ((F.metric b).isCompact_closedBall_of_metricComplete hcomplete O (3 * r))
  refine ⟨C, hCnonneg, ?_⟩
  intro s hs t ht y hy
  have hab : a ≤ b := hs.1.trans hs.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hy' : y ∈ (F.metric s).ball O r :=
    F.ball_subset_ball_of_ricci_nonneg hJ O r ha hs hs.1
      (fun τ hτ z _ v => hRic τ hτ z v) hy
  have hO : O ∈ (F.metric s).ball O r := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, RiemannianMetric.edist,
      Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr
  have hdist := F.edist_le_exp_mul_of_ricci_bound (convex_Icc a b)
    (hJ.trans interior_subset) O r C hr hs ht (fun τ hτ z hz v => by
      have hz' : (F.metric b).edist O z ≤ ENNReal.ofReal (3 * r) :=
        (F.ball_subset_ball_of_ricci_nonneg hJ O (3 * r) hs hb hs.2
          (fun q hq w _ u => hRic q hq w u) hz).le
      exact (hbound τ hτ z hz' v).trans (mul_le_mul_of_nonneg_left
        (F.antitoneOn_metric_inner_self_of_ricci_nonneg hJ z v
          (fun q hq => hRic q hq z v) hτ hb hτ.2) hCnonneg)) hO hy'
  have hfinite : ENNReal.ofReal (Real.exp (C * |t - s|)) *
      (F.metric s).edist O y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((F.metric s).edist_ne_top O y)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
    ENNReal.toReal_mono hfinite hdist

private theorem continuousOn_toReal_edist_of_ricci_nonneg_aux
    [T3Space M] [PreconnectedSpace M]
    (F : RicciFlow n M J) (hTensor : ∀ t, (F.connection t).CurvatureTensorCalculus)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (hcomplete : MetricComplete (F.metric b))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (O : M) :
    ContinuousOn (fun p : ℝ × M => ((F.metric p.1).edist O p.2).toReal)
      (Icc a b ×ˢ univ) := by
  intro p hp
  let r := ((F.metric a).edist O p.2).toReal + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hpball : ((F.metric a).edist O p.2).toReal < r := lt_add_one _
  obtain ⟨C, _, hcompare⟩ := exists_local_distance_exp_comparison F hTensor hJ hcomplete hRic O hr
  have hnear : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (F.metric a).ball O r := by
    have hh := (((F.metric a).continuous_toReal_edist O).comp continuous_snd).continuousAt
      |>.eventually_lt_const hpball
    filter_upwards [hh] with q hq
    change (F.metric a).edist O q.2 < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal ((F.metric a).edist_ne_top O q.2)]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hq
  let D : ℝ × M → ℝ := fun q => ((F.metric p.1).edist O q.2).toReal
  let E : ℝ × M → ℝ := fun q => Real.exp (C * |q.1 - p.1|)
  have hD : Continuous D := ((F.metric p.1).continuous_toReal_edist O).comp continuous_snd
  have hE : Continuous E := by dsimp only [E]; fun_prop
  have hupper : Tendsto (fun q => E q * D q) (𝓝[Icc a b ×ˢ univ] p)
      (𝓝 (((F.metric p.1).edist O p.2).toReal)) := by
    convert ((hE.mul hD).continuousAt (x := p)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Icc a b ×ˢ univ] p ≤ 𝓝 p) using 1 <;>
      first | rfl | simp [E, D]
  have hlower : Tendsto (fun q => (E q)⁻¹ * D q) (𝓝[Icc a b ×ˢ univ] p)
      (𝓝 (((F.metric p.1).edist O p.2).toReal)) := by
    convert ((hE.continuousAt.inv₀ (Real.exp_ne_zero _)).mul hD.continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Icc a b ×ˢ univ] p ≤ 𝓝 p) using 1 <;>
      first | rfl | simp [E, D]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with q hq hqy
    apply (inv_mul_le_iff₀ (Real.exp_pos _)).mpr
    simpa only [E, D, abs_sub_comm p.1 q.1] using
      hcompare q.1 hq.1 p.1 hp.1 q.2 hqy
  · filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with q hq hqy
    exact hcompare p.1 hp.1 q.1 hq.1 q.2 hqy

theorem continuousOn_toReal_edist_of_ricci_nonneg
    [T3Space M] [PreconnectedSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (hcomplete : MetricComplete (F.metric b))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (O : M) :
    ContinuousOn (fun p : ℝ × M => ((F.metric p.1).edist O p.2).toReal)
      (Icc a b ×ˢ univ) :=
  continuousOn_toReal_edist_of_ricci_nonneg_aux F
    (fun t => hC.tensor_calculus n M (F.metric t) (F.connection t)) hJ hcomplete hRic O

theorem continuousOn_toReal_edist_of_ricci_nonneg_intrinsic
    [T3Space M] [PreconnectedSpace M]
    (F : RicciFlow n M J)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (hcomplete : MetricComplete (F.metric b))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (O : M) :
    ContinuousOn (fun p : ℝ × M => ((F.metric p.1).edist O p.2).toReal)
      (Icc a b ×ˢ univ) :=
  continuousOn_toReal_edist_of_ricci_nonneg_aux F
    (fun t => (F.connection t).intrinsicCurvatureTensorCalculus) hJ hcomplete hRic O

end PoincareConjecture.RicciFlow
