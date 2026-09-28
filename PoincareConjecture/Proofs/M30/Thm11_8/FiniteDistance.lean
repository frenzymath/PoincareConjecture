import PoincareConjecture.Proofs.M30.Thm11_8.FiniteHarnack
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DistanceDistortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion.Transfer
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.Harnack
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30




theorem finite_backward_distance_bound
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u})
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    (F : RicciFlow 3 M (Ioc (-T) 0))
    (hcomplete : ∀ t ∈ Ioc (-T) 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Ioc (-T) 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ t ∈ Ioc (-T) 0, ∀ x,
      (F.connection t).scalarCurvature x ≤ Q * T / (t + T))
    (t : ℝ) (ht : t ∈ Ioc (-T) 0) (x y : M) :
    ((F.metric 0).edist x y).toReal ≤ ((F.metric t).edist x y).toReal ∧
      ((F.metric t).edist x y).toReal ≤
        ((F.metric 0).edist x y).toReal + 40 * Real.sqrt Q * T := by
  by_cases hxy : x = y
  · subst y
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero,
      zero_add]
    exact ⟨le_rfl, by positivity⟩
  by_cases ht0 : t = 0
  · subst t
    exact ⟨le_rfl, le_add_of_nonneg_right (by positivity)⟩
  have htneg : t < 0 := lt_of_le_of_ne ht.2 ht0
  let d (s : ℝ) := ((F.metric s).edist x y).toReal
  have hinner (s : ℝ) (z : M) (v : TangentSpace (𝓡 3) z) :
      0 ≤ (F.metric s).inner z v v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  have hric (s : ℝ) (hs : s ∈ Ioc (-T) 0) (z : M)
      (v : TangentSpace (𝓡 3) z) :
      0 ≤ (F.connection s).ricci z v v ∧
        (F.connection s).ricci z v v ≤ Q * T / (s + T) * (F.metric s).inner z v v := by
    obtain ⟨hlo, hhi⟩ := (F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus 3 M (F.metric s) (F.connection s)) z (hoperator s hs z) v
    exact ⟨hlo, hhi.trans
      (mul_le_mul_of_nonneg_right (hscalar s hs z) (hinner s z v))⟩
  have hIJ : Icc t 0 ⊆ Ioc (-T) 0 :=
    fun s hs => ⟨ht.1.trans_le hs.1, hs.2⟩
  let K := Q * T / (t + T)
  have hKric (s : ℝ) (hs : s ∈ Icc t 0) (z : M)
      (v : TangentSpace (𝓡 3) z) :
      |(F.connection s).ricci z v v| ≤ K * (F.metric s).inner z v v := by
    rw [abs_of_nonneg (hric s (hIJ hs) z v).1]
    apply (hric s (hIJ hs) z v).2.trans
    apply mul_le_mul_of_nonneg_right _ (hinner s z v)
    exact div_le_div_of_nonneg_left (mul_pos hQ hT).le
      (by linarith [ht.1]) (by linarith [hs.1])
  have hcompare (a b : ℝ) (ha : a ∈ Icc t 0) (hb : b ∈ Icc t 0) :
      d b ≤ Real.exp (K * |b - a|) * d a :=
    F.toReal_edist_le_exp_of_ricci_bound (convex_Icc t 0) hIJ ha hb K hKric x y
  have hcont : ContinuousOn d (Icc t 0) := by
    intro v hv
    have he : Tendsto (fun s : ℝ => Real.exp (K * |s - v|))
        (𝓝[Icc t 0] v) (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => Real.exp (K * |s - v|)) := by fun_prop
      simpa only [sub_self, abs_zero, mul_zero, Real.exp_zero] using
        (hc.continuousAt (x := v)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Icc t 0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun s => d v / Real.exp (K * |s - v|))
      (h := fun s => Real.exp (K * |s - v|) * d v)
    · simpa only [Pi.div_def, div_one, d] using
        (tendsto_const_nhds (x := d v)).div he (by norm_num : (1 : ℝ) ≠ 0)
    · simpa only [one_mul] using he.mul (tendsto_const_nhds (x := d v))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      simpa only [abs_sub_comm v s, mul_comm] using hcompare s v hs hv
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hcompare v s hv hs
  have hIinterior (b : ℝ) (hb : b ∈ Ioo t 0) : Icc t b ⊆ interior (Ioc (-T) 0) := by
    intro s hs
    rw [interior_Ioc]
    exact ⟨ht.1.trans_le hs.1, hs.2.trans_lt hb.2⟩
  have hlower (b : ℝ) (hb : b ∈ Ioo t 0) : d b ≤ d t := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hrpos : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hr
    have hy : y ∈ (F.metric t).ball x r := by
      change (F.metric t).edist x y < ENNReal.ofReal r
      rw [← ENNReal.ofReal_toReal ((F.metric t).edist_ne_top x y)]
      exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hr
    have hin := F.ball_subset_ball_of_ricci_nonneg (hIinterior b hb) x r
      (left_mem_Icc.mpr hb.1.le) (right_mem_Icc.mpr hb.1.le) hb.1.le
      (fun s hs z _ v => (hric s (hIJ ⟨hs.1, hs.2.trans hb.2.le⟩) z v).1) hy
    exact (ENNReal.toReal_lt_of_lt_ofReal hin).le
  have hterminalLower : d 0 ≤ d t :=
    Poincare.Asymptotics.le_at_right_endpoint htneg
      (hcont 0 (right_mem_Icc.mpr ht.2)) continuousWithinAt_const hlower
  let A := Real.sqrt (Q * T)
  have hA : 0 < A := Real.sqrt_pos.mpr (mul_pos hQ hT)
  have hAsq : A ^ 2 = Q * T := Real.sq_sqrt (mul_pos hQ hT).le
  let w (s : ℝ) := -40 * A * Real.sqrt (s + T)
  have hwcont : Continuous w := by dsimp only [w]; fun_prop
  have hstep (b : ℝ) (hb : b ∈ Ioo t 0) : d t - w t ≤ d b - w b := by
    have hc : ContinuousOn (fun s => d s - w s) (Icc t b) :=
      (hcont.mono (Icc_subset_Icc_right hb.2.le)).sub hwcont.continuousOn
    have hsupport (s : ℝ) (hs : s ∈ Ioc t b) :
        ∃ u : ℝ → ℝ, u s = d s - w s ∧
          (∀ r, d r - w r ≤ u r) ∧ DifferentiableAt ℝ u s ∧ - (0 : ℝ) ≤ deriv u s := by
      have hsJ : s ∈ Ioc (-T) 0 := ⟨ht.1.trans hs.1, hs.2.trans hb.2.le⟩
      have hspos : 0 < s + T := by linarith [hsJ.1]
      let z := Real.sqrt (s + T)
      have hz : 0 < z := Real.sqrt_pos.mpr hspos
      have hzsq : z ^ 2 = s + T := Real.sq_sqrt hspos.le
      have hy : y ∈ (F.metric s).ball x (d s + 1) := by
        change (F.metric s).edist x y < ENNReal.ofReal (d s + 1)
        rw [← ENNReal.ofReal_toReal ((F.metric s).edist_ne_top x y)]
        exact (ENNReal.ofReal_lt_ofReal_iff (by dsimp only [d]; positivity)).mpr
          (lt_add_one (d s))
      obtain ⟨U, rho, _hU, hyU, _hsmooth, heq, habove, _hgrad, _hlap, hd, hder⟩ :=
        F.exists_distance_spacetime_upper_support (m := 2)
          (hIinterior b hb (Ioc_subset_Icc_self hs)) (by norm_num)
          (hcomplete s hsJ) (fun q v => (hric s hsJ q v).1)
          (div_nonneg (mul_pos hQ hT).le hspos.le) (div_pos hA hz) x y hy hxy
          (fun q _ v => (hric s hsJ q v).2)
      have hcoeff : 4 * (3 : ℝ) * (A / z) + 8 * (Q * T / (s + T)) / (A / z) =
          20 * A / z := by
        rw [← hAsq, ← hzsq]
        field_simp
        ring
      change -(4 * (3 : ℝ) * (A / z) + 8 * (Q * T / (s + T)) / (A / z)) ≤
        deriv (fun r => rho r y) s at hder
      rw [hcoeff] at hder
      have hwder : HasDerivAt w (-(20 * A / z)) s := by
        have hdroot := ((hasDerivAt_id s).add_const T).sqrt hspos.ne'
        convert! hdroot.const_mul (-40 * A) using 1
        dsimp only [z, id_eq]
        ring
      have hud : HasDerivAt (fun r => rho r y - w r)
          (deriv (fun r => rho r y) s - -(20 * A / z)) s := by
        simpa only [Pi.sub_def] using hd.hasDerivAt.sub hwder
      refine ⟨fun r => rho r y - w r, ?_,
        fun r => sub_le_sub_right (habove r y hyU) _, hud.differentiableAt, ?_⟩
      · change rho s y - w s = d s - w s
        rw [heq]
      · rw [hud.deriv]
        simpa only [neg_zero] using sub_nonneg.mpr hder
    have hh := Poincare.AncientVolume.backward_image_le_add_of_upper_supports
      hb.1.le hc hsupport
    simpa only [zero_mul, add_zero] using hh
  have hterminalUpper : d t - w t ≤ d 0 - w 0 :=
    Poincare.Asymptotics.le_at_right_endpoint htneg continuousWithinAt_const
      ((hcont 0 (right_mem_Icc.mpr ht.2)).sub hwcont.continuousAt.continuousWithinAt) hstep
  have hwneg : w t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hA.le) (Real.sqrt_nonneg _)
  have hwzero : -w 0 = 40 * Real.sqrt Q * T := by
    dsimp only [w, A]
    rw [zero_add, Real.sqrt_mul hQ.le]
    calc
      -(-40 * (Real.sqrt Q * Real.sqrt T) * Real.sqrt T) =
          40 * Real.sqrt Q * (Real.sqrt T * Real.sqrt T) := by ring
      _ = 40 * Real.sqrt Q * T := by rw [Real.mul_self_sqrt hT.le]
  exact ⟨hterminalLower, by linarith⟩

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem exists_finite_limit_distance_error
    (hC : RicciFlowCurvatureTheory.{u}) (hH : HarnackAncientTheory.{u})
    {T : ℝ} (L : BlowupLimitFlow.{u} (Ioc (-T) 0)) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Ioc (-T) 0,
      ∀ x y : L.carrier.carrier,
        ((L.flow.metric 0).edist x y).toReal ≤
          ((L.flow.metric t).edist x y).toReal ∧
        ((L.flow.metric t).edist x y).toReal ≤
          ((L.flow.metric 0).edist x y).toReal + D := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  have hT : 0 < T := by linarith [L.zero_mem.1]
  obtain ⟨Q, hQ, hscalar⟩ := exists_finite_limit_scalar_bound hC hH L
  refine ⟨40 * Real.sqrt Q * T, by positivity, ?_⟩
  intro t ht x y
  exact finite_backward_distance_bound hC hT hQ L.flow L.complete
    L.nonnegative_curvature_operator hscalar t ht x y

end PoincareConjecture.M30
