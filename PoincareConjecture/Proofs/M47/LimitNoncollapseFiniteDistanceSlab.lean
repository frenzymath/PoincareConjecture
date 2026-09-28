import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteDistanceEndpoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DistanceDistortion









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
    ConnectedSpace L.carrier.carrier := L.connectedSpace

private theorem interior_slab (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    {a b scale : ℝ} (ha : -H.toReal < a) (hab : a ≤ b) (hb : b < 0)
    (hscale : 0 < scale) (x y : L.carrier.carrier) :
    ((L.flow.metric a).edist x y).toReal ≤ ((L.flow.metric b).edist x y).toReal +
      (12 * scale + 8 * (Q * H.toReal / (a + H.toReal)) / scale) * (b - a) := by
  have hJ : Icc a b ⊆ interior (blowupBackwardInterval H) := by
    rw [limitFinite_interior_eq hfinite]
    exact fun _ hτ => ⟨ha.trans_le hτ.1, hτ.2.trans_lt hb⟩
  have hΛ : 0 ≤ Q * H.toReal / (a + H.toReal) :=
    div_nonneg (mul_nonneg hQ.le (limitFinite_horizon_pos hH hfinite).le) (by linarith)
  have hlocal : ∀ τ ∈ Icc a b, ∃ r : ℝ, y ∈ (L.flow.metric τ).ball x r ∧
      ∀ z ∈ (L.flow.metric τ).ball x r, ∀ v : TangentSpace (𝓡 3) z,
        (L.flow.connection τ).ricci z v v ≤
          (Q * H.toReal / (a + H.toReal)) * (L.flow.metric τ).inner z v v := by
    intro τ hτ
    refine ⟨((L.flow.metric τ).edist x y).toReal + 1, ?_, fun z _ v =>
      (limitFinite_ricci_slab h04 hH hfinite L hQ hQ0 ha hb.le τ hτ z v).2⟩
    change (L.flow.metric τ).edist x y < _
    conv_lhs => rw [← ENNReal.ofReal_toReal ((L.flow.metric τ).edist_ne_top x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 1))) L.carrier.carrier :=
    L.carrier.chartedSpace
  let : IsManifold (𝓡 (2 + 1)) ∞ L.carrier.carrier := L.carrier.isManifold
  have h := RicciFlow.toReal_edist_le_add_of_ricci_upper_on_balls h04 L.flow
    (by norm_num : 0 < (2 : ℕ)) hab hJ
    (fun τ hτ => L.complete τ (interior_subset (hJ hτ)))
    (fun τ hτ z v => (limitFinite_ricci_bounds h04 L τ (interior_subset (hJ hτ)) z v).1)
    hΛ hscale x y hlocal
  norm_num only [Nat.cast_ofNat] at h
  exact h


theorem limitFinite_distance_slab (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {Q : ℝ} (hQ : 0 < Q)
    (hQ0 : ∀ x : L.carrier.carrier, (L.flow.connection 0).scalarCurvature x ≤ Q)
    {a b scale : ℝ} (ha : -H.toReal < a) (hab : a ≤ b) (hb : b ≤ 0)
    (hscale : 0 < scale) (x y : L.carrier.carrier) :
    ((L.flow.metric a).edist x y).toReal ≤ ((L.flow.metric b).edist x y).toReal +
      (12 * scale + 8 * (Q * H.toReal / (a + H.toReal)) / scale) * (b - a) := by
  rcases lt_or_eq_of_le hb with hbneg | rfl
  · exact interior_slab h04 hH hfinite L hQ hQ0 ha hab hbneg hscale x y
  rcases lt_or_eq_of_le hab with haneg | rfl
  · have hzero : (0 : ℝ) ∈ closure (Ioo a 0) := by
      rw [closure_Ioo haneg.ne]
      exact ⟨haneg.le, le_rfl⟩
    have hsub : Ioo a 0 ⊆ blowupBackwardInterval H := by
      rw [limitFinite_domain_eq hfinite]
      exact fun _ hτ => ⟨ha.trans hτ.1, hτ.2.le⟩
    have hc : ContinuousWithinAt (fun τ => ((L.flow.metric τ).edist x y).toReal)
        (blowupBackwardInterval H) 0 :=
      limitFinite_distance_tendsto_zero h04 hH hfinite L hQ hQ0 x y
    exact ContinuousWithinAt.closure_le hzero continuousWithinAt_const
      ((hc.mono hsub).add (continuousWithinAt_const.mul
        (continuousWithinAt_id.sub continuousWithinAt_const)))
      (fun τ hτ => interior_slab h04 hH hfinite L hQ hQ0 ha hτ.1.le hτ.2 hscale x y)
  · simp

end PoincareConjecture.M47
