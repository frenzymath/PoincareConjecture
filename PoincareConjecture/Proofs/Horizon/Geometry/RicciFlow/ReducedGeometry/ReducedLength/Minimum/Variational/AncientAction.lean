import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.AncientLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ActionLowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.CompactTime













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in


theorem exists_spatial_minimizing_weak_action (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (γ : ℝ → M) (m : ℕ) (t : Fin (m + 1) → ℝ)
      (x : Fin m → M) (Q : Fin m → Set M)
      (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ)),
      Continuous γ ∧ γ 0 = p ∧
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last m) = Real.sqrt τ ∧
      (∀ i, IsCompact (Q i) ∧
        γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (Q i) ∧
        Q i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source) ∧
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
          ∫ r in t i.castSucc..s, w i r) ∧
      (∑ i : Fin m,
        ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric K.flow 0 (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (γ s))) ≤
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ := by
  classical
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  obtain ⟨paths, γ, m, t, x, Q, v, w, B, hstart, hanti, haction, hγ, hγ0,
    hlim, ht, ht0, htend, hQ, hαQ, hv, hprimitive, hweak⟩ :=
    K.exists_spatial_minimizing_chart_limit p hτ
  let α : ℕ → ℝ → M := fun k s => (paths k).curve (s ^ 2)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (i : Fin m) : 0 ≤ t i.castSucc := by
    rw [← ht0]
    exact ht (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ Real.sqrt τ := by
    rw [← htend]
    exact ht (Fin.le_last _)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 (Real.sqrt τ) :=
    Icc_subset_Icc (hleft i) (hright i)
  have hsuboo (i : Fin m) : Ioo (t i.castSucc) (t i.succ) ⊆ Ioo 0 (Real.sqrt τ) :=
    Ioo_subset_Ioo (hleft i) (hright i)
  have hα (i : Fin m) (k : ℕ) : ContinuousOn (α k) (Icc (t i.castSucc) (t i.succ)) := by
    apply (paths k).continuous.comp (continuous_id.pow 2).continuousOn
    intro s hs
    exact ⟨sq_nonneg s, (Real.le_sqrt (hsub i hs).1 hτ.le).mp (hsub i hs).2⟩
  have hreg (i : Fin m) (k : ℕ) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 (α k) (Ioo (t i.castSucc) (t i.succ)) := by
    apply (paths k).regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    intro s hs
    exact ⟨sq_pos_of_pos (hsuboo i hs).1,
      (Real.lt_sqrt (hsuboo i hs).1.le).mp (hsuboo i hs).2⟩
  have hγQ (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ)) (Q i) :=
    fun s hs => interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs))
  have hpotential (i : Fin m) : ContinuousOn
      (fun z : ℝ × M =>
        2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t i.castSucc) (t i.succ) ×ˢ Q i) :=
    K.regularizedPotential_continuousOn (hleft i) (hseg i) (Q i)
  have hpiece (i : Fin m) (k : ℕ) : IntervalIntegrable
      (regularizedLIntegrand K.flow 0 (α k)) volume (t i.castSucc) (t i.succ) := by
    apply (squarePath_action (paths k)).1.mono_set
    simpa only [uIcc_of_le (hseg i), uIcc_of_le (Real.sqrt_nonneg τ)] using hsub i
  have henergy (k : ℕ) :
      (∑ i : Fin m,
        ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric K.flow 0 (x i) (s, α k s) (v i k s) (v i k s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (α k s))) ≤
        backwardLLength K.flow 0 0 τ (paths k).curve := by
    have heq (i : Fin m) := chart_piece_action_eq K.flow 0 (hseg i) (x i) (α k)
      (hreg i k) (fun s hs => (hQ i).2.2 (hαQ i k hs))
      ((hpotential i).comp (continuousOn_id.prodMk (hα i k))
        (fun s hs => ⟨hs, hαQ i k hs⟩)) (hpiece i k) (v i k) (hv i k).2
    simp_rw [heq]
    have hsum := sum_integral_fin_partition t ht (regularizedLIntegrand K.flow 0 (α k))
      (by simpa only [ht0, htend] using (squarePath_action (paths k)).1)
    rw [hsum, ht0, htend]
    exact (squarePath_action (paths k)).2.le
  refine ⟨γ, m, t, x, Q, w, hγ, hγ0, ht, ht0, htend, hQ, hprimitive, ?_⟩
  exact @finite_chart_action_le 2 M (referenceMetricSpace (K.flow.metric 0))
    inferInstance inferInstance (Iic 0) K.flow 0 (Fin m) inferInstance
    (fun i => t i.castSucc) (fun i => t i.succ)
    hseg x Q (fun i => (hQ i).1) (fun i => (hQ i).2.2)
    (fun _ s _ => show 0 - s ^ 2 ∈ Iic 0 from by
      exact sub_nonpos.mpr (sq_nonneg s))
    hpotential α γ hα (fun _ => hγ.continuousOn) hαQ hγQ
    (fun i => hlim.mono (hsub i)) v w B (fun i k => (hv i k).1) hweak
    (fun k => backwardLLength K.flow 0 0 τ (paths k).curve)
    (2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) haction henergy

end PoincareConjecture.AncientKappaSolution
