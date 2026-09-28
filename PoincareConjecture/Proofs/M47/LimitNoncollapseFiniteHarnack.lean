import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteHarnackDomain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.BoundedFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Path.Comparison

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    SecondCountableTopology L.carrier.carrier := L.carrier.secondCountable
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ConnectedSpace L.carrier.carrier := L.connectedSpace

theorem limitFinite_interior_harnack (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H))
    {a b : ℝ} (ha : -H.toReal < a) (hab : a < b) (hb : b < 0)
    (x : L.carrier.carrier) :
    (L.flow.connection a).scalarCurvature x * (a + H.toReal) ≤
      (L.flow.connection b).scalarCurvature x * (b + H.toReal) := by
  let F := limitFiniteOpenFlow hH hfinite L
  have hsub : Ioo (-H.toReal) 0 ⊆ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    exact Ioo_subset_Ioc_self
  have hc : ∀ t ∈ Ioo (-H.toReal) 0, MetricComplete (F.metric t) :=
    fun t ht => L.complete t (hsub ht)
  have hn : ∀ t ∈ Ioo (-H.toReal) 0, ∀ y,
      (F.connection t).NonnegativeCurvatureOperator y :=
    fun t ht => L.nonnegative_curvature_operator t (hsub ht)
  have hbound : ∀ c d : ℝ, c < d → Icc c d ⊆ Ioo (-H.toReal) 0 →
      ∃ K : ℝ, ∀ s ∈ Icc c d, ∀ y, (F.connection s).curvatureTensorNorm y ≤ K := by
    intro c d _ hcd
    obtain ⟨K, _, hK⟩ := L.curvature_locally_bounded_in_time (Icc c d)
      isCompact_Icc (hcd.trans hsub)
    exact ⟨K, fun s hs y => (le_abs_self _).trans (hK s hs y)⟩
  have hdiff := Poincare.RicciFlow.Harnack.finite_differential_of_curvature_slab_bounds
    h04 F hc hn hbound
  have hi := Poincare.Geometry.RicciFlow.Harnack.finite_integrated_of_differential
    h04 ha hab hb F hn hdiff (fun _ => x) contMDiffOn_const rfl rfl
  simpa [spacetimeEnergy, F, limitFiniteOpenFlow,
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow] using hi

theorem limitFinite_weighted_scalar (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H))
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (x : L.carrier.carrier) :
    0 ≤ (L.flow.connection t).scalarCurvature x ∧
      (L.flow.connection t).scalarCurvature x * (t + H.toReal) ≤
        (L.flow.connection 0).scalarCurvature x * H.toReal := by
  refine ⟨limitFinite_scalar_nonneg h04 L t ht x, ?_⟩
  have ht' : t ∈ Ioc (-H.toReal) 0 := by rwa [← limitFinite_domain_eq hfinite]
  rcases lt_or_eq_of_le ht'.2 with hneg | rfl
  · have hsub : Ioo t 0 ⊆ blowupBackwardInterval H := by
      rw [limitFinite_domain_eq hfinite]
      exact fun _ hs => ⟨ht'.1.trans hs.1, hs.2.le⟩
    have hc := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_contDiffOn_time
      h04 _ L.flow x).continuousOn 0 L.zero_mem
    have hzero : (0 : ℝ) ∈ closure (Ioo t 0) := by
      rw [closure_Ioo hneg.ne]
      exact ⟨hneg.le, le_rfl⟩
    have h := ContinuousWithinAt.closure_le hzero continuousWithinAt_const
      ((hc.mono hsub).mul (continuousWithinAt_id.add continuousWithinAt_const))
      (fun b hb => limitFinite_interior_harnack h04 hH hfinite L ht'.1 hb.1 hb.2 x)
    simpa only [Pi.mul_apply, Pi.add_apply, id_eq, zero_add] using h
  · simp

theorem limitFinite_scalar_le (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ}
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (x : L.carrier.carrier) :
    (L.flow.connection t).scalarCurvature x ≤ Q * H.toReal / (t + H.toReal) := by
  have ht' : t ∈ Ioc (-H.toReal) 0 := by rwa [← limitFinite_domain_eq hfinite]
  apply (le_div_iff₀ (by linarith [ht'.1] : 0 < t + H.toReal)).mpr
  exact (limitFinite_weighted_scalar h04 hH hfinite L t ht x).2.trans
    (mul_le_mul_of_nonneg_right (hQ0 x) (limitFinite_horizon_pos hH hfinite).le)

theorem limitFinite_scalar_harnack (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {B0 : ℝ}
    (hterminal : ∀ x : L.carrier.carrier,
      (L.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) (x : L.carrier.carrier) :
    0 ≤ (L.flow.connection t).scalarCurvature x ∧
      (L.flow.connection t).scalarCurvature x * (t + H.toReal) ≤
        max 1 (3 * B0) * H.toReal := by
  have h := limitFinite_weighted_scalar h04 hH hfinite L t ht x
  refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right ?_
    (limitFinite_horizon_pos hH hfinite).le)⟩
  exact ((L.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp x).trans
    ((mul_le_mul_of_nonneg_left (hterminal x) (by norm_num)).trans (le_max_right _ _))

theorem limitFinite_ricci_slab (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    {a b : ℝ} (ha : -H.toReal < a) (hb : b ≤ 0)
    (t : ℝ) (ht : t ∈ Icc a b) (x : L.carrier.carrier)
    (v : TangentSpace (𝓡 3) x) :
    0 ≤ (L.flow.connection t).ricci x v v ∧
      (L.flow.connection t).ricci x v v ≤
        (Q * H.toReal / (a + H.toReal)) * (L.flow.metric t).inner x v v := by
  have htJ : t ∈ blowupBackwardInterval H := by
    rw [limitFinite_domain_eq hfinite]
    exact ⟨ha.trans_le ht.1, ht.2.trans hb⟩
  have hRic := limitFinite_ricci_bounds h04 L t htJ x v
  have hscalar := limitFinite_scalar_le h04 hH hfinite L hQ0 t htJ x
  have hle : Q * H.toReal / (t + H.toReal) ≤ Q * H.toReal / (a + H.toReal) :=
    div_le_div_of_nonneg_left (mul_nonneg hQ.le (limitFinite_horizon_pos hH hfinite).le)
      (by linarith) (by linarith [ht.1])
  have hg : 0 ≤ (L.flow.metric t).inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact ((L.flow.metric t).pos x v hv).le
  exact ⟨hRic.1, hRic.2.trans (mul_le_mul_of_nonneg_right (hscalar.trans hle) hg)⟩

end PoincareConjecture.M47
