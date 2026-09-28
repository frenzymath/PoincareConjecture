import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

theorem monotoneOn_weighted_scalar_on_Ioc
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hH : HarnackAncientTheory.{u})
    {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Ioc a b))
    (hcomplete : ∀ t ∈ Ioc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Ioc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbounded : ∀ t ∈ Ioc a b, ∃ B : ℝ, 0 ≤ B ∧
      ∀ x, (F.connection t).curvatureTensorNorm x ≤ B)
    (x : M) :
    MonotoneOn (fun t => (t - a) * (F.connection t).scalarCurvature x) (Ioc a b) := by
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    Ioo_subset_Ioc_self ordConnected_Ioo
    (show (Ioo a b).Nontrivial from
      ⟨(2 * a + b) / 3, ⟨by linarith, by linarith⟩,
        (a + 2 * b) / 3, ⟨by linarith, by linarith⟩, by linarith⟩)
  have hbound (t : ℝ) (ht : t ∈ Ioo a b) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y : M,
        LeviCivitaData.CurvatureOperatorBound (G.connection t) B y := by
    obtain ⟨B, hB, hb⟩ := hbounded t (Ioo_subset_Ioc_self ht)
    refine ⟨(n : ℝ) ^ 2 * B, mul_nonneg (sq_nonneg _) hB, ?_⟩
    intro y A hA
    have hscalar : (F.connection t).scalarCurvature y ≤ (n : ℝ) ^ 2 * B :=
      (le_abs_self _).trans
        (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm y).trans
          (mul_le_mul_of_nonneg_left (hb y) (sq_nonneg _)))
    exact (((F.connection t).curvatureOperatorBound_scalarCurvature
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) y
      (hoperator t (Ioo_subset_Ioc_self ht) y)).2 A hA).trans
        (mul_le_mul_of_nonneg_right hscalar (by positivity))
  have hharnack (t : ℝ) (ht : t ∈ Ioo a b) :
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a) := by
    obtain ⟨dR, hdR, hineq⟩ := hH.finite_differential n M a b hab G
      (fun s hs => hcomplete s (Ioo_subset_Ioc_self hs))
      (fun s hs => hoperator s (Ioo_subset_Ioc_self hs)) hbound t ht x 0
    have hevolution := (hC.scalar_evolution n M (Ioc a b) F t
      (Ioo_subset_Ioc_self ht) x).mono Ioo_subset_Ioc_self
    have heq := (hdR.hasDerivAt (isOpen_Ioo.mem_nhds ht)).unique
      (hevolution.hasDerivAt (isOpen_Ioo.mem_nhds ht))
    have hzero : (F.connection t).ricci x 0 0 = 0 := by
      rw [LeviCivitaData.ricci_eq_sum_frame]
      simp only [map_zero, mul_zero, Finset.sum_const_zero]
    change 0 ≤ dR + (F.connection t).scalarCurvature x / (t - a) +
      2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x 0 +
      2 * (F.connection t).ricci x 0 0 at hineq
    simpa only [heq, map_zero, hzero, mul_zero, add_zero] using hineq
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc a b)
    ((continuousOn_id.sub continuousOn_const).mul
      (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
        hC (Ioc a b) F x))
    (f' := fun t => (F.connection t).scalarCurvature x + (t - a) *
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x))
  · intro t ht
    rw [interior_Ioc] at ht ⊢
    have hd := (hC.scalar_evolution n M (Ioc a b) F t
      (Ioo_subset_Ioc_self ht) x).mono Ioo_subset_Ioc_self
    simpa only [one_mul, id_eq, Pi.mul_def, Pi.sub_def] using
      ((hasDerivWithinAt_id t (Ioo a b)).sub_const a).mul hd
  · intro t ht
    rw [interior_Ioc] at ht
    have hpos : 0 < t - a := sub_pos.mpr ht.1
    have h := mul_nonneg hpos.le (hharnack t ht)
    rw [mul_add, mul_div_cancel₀ _ hpos.ne'] at h
    linarith

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_finite_limit_scalar_bound
    (hC : RicciFlowCurvatureTheory.{u}) (hH : HarnackAncientTheory.{u})
    {T : ℝ} (L : BlowupLimitFlow.{u} (Ioc (-T) 0)) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ t ∈ Ioc (-T) 0,
      ∀ x : L.carrier.carrier,
        (L.flow.connection t).scalarCurvature x ≤ Q * T / (t + T) := by
  have hT : 0 < T := by linarith [L.zero_mem.1]
  have hbounded (t : ℝ) (ht : t ∈ Ioc (-T) 0) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : L.carrier.carrier,
        (L.flow.connection t).curvatureTensorNorm x ≤ B := by
    obtain ⟨B, hB, hb⟩ := L.curvature_locally_bounded_in_time {t}
      isCompact_singleton (singleton_subset_iff.mpr ht)
    exact ⟨B, hB, fun x => (le_abs_self _).trans (hb t (mem_singleton t) x)⟩
  obtain ⟨B, _hB, hb⟩ := hbounded 0 L.zero_mem
  refine ⟨max 1 (9 * B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht x
  have hterminal : (L.flow.connection 0).scalarCurvature x ≤ max 1 (9 * B) := by
    have h := (le_abs_self _).trans
      (((L.flow.connection 0).abs_scalarCurvature_le_curvatureTensorNorm x).trans
        (mul_le_mul_of_nonneg_left (hb x) (sq_nonneg (3 : ℝ))))
    norm_num only [Nat.cast_ofNat, sq] at h
    exact h.trans (le_max_right _ _)
  have hmono := monotoneOn_weighted_scalar_on_Ioc hC hH
    (show -T < 0 by linarith) L.flow L.complete
    L.nonnegative_curvature_operator hbounded x ht L.zero_mem ht.2
  have hweight := mul_le_mul_of_nonneg_left hterminal hT.le
  apply (le_div_iff₀ (show 0 < t + T by linarith [ht.1])).mpr
  simp only [sub_neg_eq_add, zero_add] at hmono
  nlinarith

end PoincareConjecture.M30
