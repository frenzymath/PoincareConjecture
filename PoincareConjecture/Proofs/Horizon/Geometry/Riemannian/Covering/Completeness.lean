import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.TotallyDisconnected











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem metricComplete_of_isCoveringMap
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    [T3Space M] [T3Space N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 m) ∞ F) (hcover : IsCoveringMap F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (F x)
        (mfderiv (𝓡 n) (𝓡 m) F x v) (mfderiv (𝓡 n) (𝓡 m) F x w))
    (hc : MetricComplete gN) : MetricComplete gM := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨gM.inner, gM.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : N → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 m) N
  let : CompleteSpace N := hc
  have hLip : LipschitzWith 1 F := by
    intro x y
    change gN.edist (F x) (F y) ≤ (1 : ℝ≥0∞) * gM.edist x y
    simpa only [one_mul] using edist_map_le_of_metric_pullback gM gN hF hinner x y
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (hLip.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨hd, U, hyU, hU, _, H, hH⟩ := hcover y
  let : DiscreteTopology (F ⁻¹' {y}) := hd
  obtain ⟨r, hr, hrU⟩ := EMetric.mem_nhds_iff.mp (hU.mem_nhds hyU)
  have hr2 : 0 < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨a, ha⟩ := (EMetric.cauchySeq_iff.mp hu) (r / 2) hr2
  obtain ⟨b, hb⟩ := eventually_atTop.mp
    (hy.eventually (Metric.eball_mem_nhds y hr2))
  let k := max a b
  have hbase (j : ℕ) : F (u (j + k)) ∈ U := by
    apply hrU
    exact (hb _ (le_trans (le_max_right a b) (Nat.le_add_left k j))).trans_le
      ENNReal.half_le_self
  let v (j : ℕ) : F ⁻¹' U := ⟨u (j + k), hbase j⟩
  have hsheet (j : ℕ) : (H (v j)).2 = (H (v 0)).2 := by
    have hclose : gM.edist (u k) (u (j + k)) < r / 2 :=
      ha k (le_max_left a b) (j + k)
        (le_trans (le_max_left a b) (Nat.le_add_left k j))
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hclose zero_lt_one
    have hstay (t : Set.Icc (0 : ℝ) 1) : F (γ t) ∈ U := by
      apply hrU
      have hdist : EDist.edist (u k) (γ t) < r / 2 :=
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn h0 rfl t.2.1).trans_lt
          ((Manifold.pathELength_mono le_rfl t.2.2).trans_lt hlen)
      have hmap : EDist.edist (F (γ t)) (F (u k)) < r / 2 := by
        have hle := hLip (γ t) (u k)
        simp only [ENNReal.coe_one, one_mul] at hle
        exact hle.trans_lt (by simpa [edist_comm] using hdist)
      exact (edist_triangle _ (F (u k)) y).trans_lt
        ((ENNReal.add_lt_add hmap (hb k (le_max_right a b))).trans_eq
          (ENNReal.add_halves r))
    let Γ (t : Set.Icc (0 : ℝ) 1) : F ⁻¹' U := ⟨γ t, hstay t⟩
    have hΓ : Continuous Γ :=
      (hγ.continuous.comp continuous_subtype_val).subtype_mk hstay
    have hconst : (H (Γ ⟨1, by simp⟩)).2 = (H (Γ ⟨0, by simp⟩)).2 :=
      (inferInstance : PreconnectedSpace (Set.Icc (0 : ℝ) 1)).constant
        (continuous_snd.comp (H.continuous.comp hΓ))
    have hΓ0 : Γ ⟨0, by simp⟩ = v 0 := by
      apply Subtype.ext
      simpa [Γ, v] using h0
    have hΓ1 : Γ ⟨1, by simp⟩ = v j := by
      apply Subtype.ext
      exact h1
    simpa only [hΓ0, hΓ1] using hconst
  let z : U × (F ⁻¹' {y}) := (⟨y, hyU⟩, (H (v 0)).2)
  have hvbase : Tendsto (fun j => (H (v j)).1) atTop (𝓝 z.1) := by
    apply tendsto_subtype_rng.mpr
    have hshift := hy.comp (tendsto_add_atTop_nat k)
    simpa only [Function.comp_def, hH, v, z] using hshift
  have hv : Tendsto (fun j => H (v j)) atTop (𝓝 z) := by
    apply hvbase.prodMk_nhds
    exact tendsto_const_nhds.congr (fun j => (hsheet j).symm)
  have hlim : Tendsto (fun j => u (j + k)) atTop (𝓝 (H.symm z).1) := by
    have := (continuous_subtype_val.continuousAt.tendsto.comp
      (H.symm.continuous.continuousAt.tendsto.comp hv))
    simpa only [Function.comp_def, H.symm_apply_apply, v] using this
  exact ⟨(H.symm z).1, (tendsto_add_atTop_iff_nat k).mp hlim⟩



theorem metricComplete_pullbackOfLocalDiffeomorph
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    [T3Space M] [T3Space N]
    (g : RiemannianMetric n N) (F : M → N)
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F)
    (hcover : IsCoveringMap F) (hc : MetricComplete g) :
    MetricComplete (g.pullbackOfLocalDiffeomorph F hF) :=
  metricComplete_of_isCoveringMap _ g hF.contMDiff hcover (fun _ _ _ => rfl) hc

end PoincareConjecture.RiemannianMetric
