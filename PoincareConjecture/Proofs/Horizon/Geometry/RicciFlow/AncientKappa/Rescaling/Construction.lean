import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Rescaling.SetupTheory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private noncomputable def ancientRescalingOfTheory
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (K : AncientKappaSolution n M) (tau : ℝ) (htau : 0 < tau) :
    AncientRescaling K tau := by
  let I : SpacetimeInterval := ⟨Iic 0, ordConnected_Iic,
    ⟨-1, by norm_num, 0, by simp, by norm_num⟩⟩
  have hQ : 0 < 1 / tau := one_div_pos.mpr htau
  let R := Classical.choice (hM13.ordinary_flow M I K.flow (1 / tau) hQ 0)
  have htime (s : ℝ) : parabolicTimeInv (1 / tau) 0 s = tau * s := by
    simp [parabolicTimeInv, mul_comm]
  have hsub : Iio 0 ⊆ (parabolicInterval (1 / tau) hQ 0 I).domain := by
    intro s hs
    rw [mem_parabolicInterval_iff]
    change parabolicTimeInv (1 / tau) 0 s ≤ 0
    rw [htime]
    exact mul_nonpos_of_nonneg_of_nonpos htau.le hs.le
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub
    ordConnected_Iio ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩
  have hcal (s : ℝ) : MetricHomothetyCalculus (K.flow.metric (tau * s))
      (G.metric s) (Diffeomorph.refl (𝓡 n) M ∞) (1 / tau) := by
    change MetricHomothetyCalculus (K.flow.metric (tau * s))
      (R.flow.metric s) (Diffeomorph.refl (𝓡 n) M ∞) (1 / tau)
    rw [← htime]
    exact R.metric_calculus s
  exact {
    tau_pos := htau
    flow := G
    metric_scale := by
      intro s _ x v w
      change (R.flow.metric s).inner x v w = _
      rw [← htime]
      exact R.metric_eq s x v w
    ricci_scale := by
      intro s _ x v w
      have h := (hcal s).ricci_eq (K.flow.connection (tau * s)) (G.connection s) x v w
      simp only [Diffeomorph.coe_refl, mfderiv_id] at h
      change (G.connection s).ricci x v w =
        (K.flow.connection (tau * s)).ricci x v w at h
      exact h
    scalar_scale := by
      intro s _ x
      simpa only [Diffeomorph.coe_refl, id_eq, one_div, div_inv_eq_mul, mul_comm]
        using (hcal s).scalar_eq (K.flow.connection (tau * s)) (G.connection s) x
    curvature_norm_scale := by
      intro s _ x
      simpa only [Diffeomorph.coe_refl, id_eq, one_div, div_inv_eq_mul, mul_comm]
        using (hcal s).curvature_norm_eq (K.flow.connection (tau * s)) (G.connection s) x }

theorem horizon_ancientBlowupSequenceSetup (n : ℕ)
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ)
    (tau_pos : ∀ k, 0 < tau k)
    (tau_tendsto : Filter.Tendsto tau Filter.atTop Filter.atTop)
    (hM10 : AncientReducedVolumeMinimumProvider K)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    AncientBlowupSetupConclusion K reference tau := by
  classical
  have hmin (k : ℕ) : ∃ q : M,
      (∀ y : M, reducedLength K.flow 0 reference q (tau k) ≤
        reducedLength K.flow 0 reference y (tau k)) ∧
      reducedLength K.flow 0 reference q (tau k) ≤ (n : ℝ) / 2 := by
    let V := Classical.choice (hM10 (tau k + 1) (by linarith [tau_pos k]))
    exact V.minimum_bound reference (tau k) (tau_pos k) (by linarith)
  choose base hbase hbound using hmin
  exact ⟨{
    sequence := {
      reference := reference
      scale := tau
      scale_pos := tau_pos
      scale_tendsto := tau_tendsto
      rescaling := fun k ↦ ancientRescalingOfTheory hM13 K (tau k) (tau_pos k)
      base := base
      base_minimizing := hbase
      base_reduced_length_bound := hbound }
    reference_eq := rfl
    scale_eq := rfl }⟩

end PoincareConjecture
