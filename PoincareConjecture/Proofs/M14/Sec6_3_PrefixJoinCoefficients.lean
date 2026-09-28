import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinGauge
import PoincareConjecture.Proofs.M14.Sec6_2_ContinuousPotential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14.PrefixJoinGauge

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}
  {q : M14BackwardPath G T τ₁ τ₂ x y}
  {p : M14BackwardPath G T τ₁ c x (q.curve c)} (D : PrefixJoinGauge q p)

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem clock_contMDiffOn_one :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) 1 (fun s => (D.lift (q.curve s)).1)
      (Icc (c - D.radius) (c + D.radius)) := by
  have hsub : Icc (c - D.radius) (c + D.radius) ⊆ Ioo τ₁ τ₂ :=
    fun _ hs => ⟨D.left_margin.trans_le hs.1, hs.2.trans_lt D.right_margin⟩
  have hL := (D.lift_smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp
    (q.curve_regular.mono hsub) D.continuation_in_image
  exact fun s hs => (hL s hs).fst

theorem exists_coefficient_bound (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    let x₀ := (D.lift (q.curve c)).2
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (c - D.radius) (c + D.radius), ∀ v ∈ D.spatialRegion,
      ‖backwardMetricCoefficient (G.gaugeCover.spatial D.index)
        (G.gaugeCover.metric D.index).metric T x₀ (s, v)‖ ≤ C ∧
      ‖backwardPotentialCoefficient D.index (fun t => (D.lift (q.curve t)).1) x₀ (s, v)‖ ≤ C := by
  dsimp only
  let J := Icc (c - D.radius) (c + D.radius)
  let x₀ := (D.lift (q.curve c)).2
  let B := backwardMetricCoefficient (G.gaugeCover.spatial D.index)
    (G.gaugeCover.metric D.index).metric T x₀
  let V := backwardPotentialCoefficient D.index (fun t => (D.lift (q.curve t)).1) x₀
  have hpos : ∀ s ∈ J, 0 < s :=
    fun _ hs => (p.tau_nonneg.trans_lt D.left_margin).trans_le hs.1
  have htime : ∀ s ∈ J, T - s ∈ (G.gaugeCover.interval D.index).domain := by
    intro s hs
    have ht := (D.lift_time _ (D.continuation_in_image s hs)).trans
      (q.curve_time s ⟨D.left_margin.le.trans hs.1, hs.2.trans D.right_margin.le⟩)
    rw [← ht]
    exact (D.lift (q.curve s)).1.property
  have hM : ContinuousOn B (J ×ˢ D.spatialRegion) :=
    (backwardMetricCoefficient_contDiffOn (G.gaugeCover.spatial D.index)
      (G.gaugeCover.metric D.index).metric (G.gaugeCover.metric D.index).smooth
      T x₀ hpos htime).continuousOn.mono (fun _ hz => ⟨hz.1, D.region_subset hz.2⟩)
  have hV : ContinuousOn V (J ×ˢ D.spatialRegion) :=
    (backwardPotentialCoefficient_continuousOn hM12 D.index
      (fun t => (D.lift (q.curve t)).1) x₀ D.clock_contMDiffOn_one.continuousOn).mono
        (fun _ hz => ⟨hz.1, D.region_subset hz.2⟩)
  have hcompact : IsCompact (J ×ˢ D.spatialRegion) := isCompact_Icc.prod D.region_compact
  obtain ⟨CM, hCM⟩ := hcompact.exists_bound_of_continuousOn hM
  obtain ⟨CV, hCV⟩ := hcompact.exists_bound_of_continuousOn hV
  refine ⟨max (max CM CV) 0, le_max_right _ _, ?_⟩
  intro s hs v hv
  exact ⟨(hCM (s, v) ⟨hs, hv⟩).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hCV (s, v) ⟨hs, hv⟩).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

end PoincareConjecture.M14.PrefixJoinGauge
