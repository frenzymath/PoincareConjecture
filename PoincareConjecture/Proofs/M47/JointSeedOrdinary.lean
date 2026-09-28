import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CompactCurvatureBound
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem jointSeed_completeBoundedCurvatureOn
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [CompactSpace M] {b t : ℝ}
    (F : RicciFlow 3 M (Icc b t)) : CompleteBoundedCurvatureOn F (Icc b t) := by
  constructor
  · intro s _hs
    rw [RiemannianMetric.metricComplete_iff_toEMetricSpace]
    let : EMetricSpace M := (F.metric s).toEMetricSpace
    infer_instance
  · have hcompact : IsCompact (Icc b t ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
    obtain ⟨K, hK⟩ := hcompact.bddAbove_image (M34.continuousOn_flow_curvatureTensorNorm F)
    refine ⟨max 0 K, le_max_left _ _, ?_⟩
    intro s hs x
    have hnorm : 0 ≤ (F.connection s).curvatureTensorNorm x := Real.sqrt_nonneg _
    rw [abs_of_nonneg hnorm]
    exact (hK ⟨(s, x), ⟨hs, mem_univ x⟩, rfl⟩).trans (le_max_right _ _)

theorem exists_jointSeed_low_action_path
    (P : M14OrdinaryProviders.{u} 3)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M] [CompactSpace M]
    {b t eta : ℝ} (hbt : b < t) (heta : 0 < eta) (hetaAge : eta < t - b)
    (F : RicciFlow 3 M (Icc b t)) (x : M) :
    ∃ _hL : LGeodesicTheory F t (t - b),
      ∃ path : BackwardTimePath F t 0 (t - b - eta),
        path.curve 0 = x ∧ IsMinimizingBackwardLPath F t 0 (t - b - eta) path ∧
        backwardLLength F t 0 (t - b - eta) path.curve ≤ 3 * Real.sqrt (t - b) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hd : 0 < t - b := sub_pos.mpr hbt
  have ht : t ∈ Icc b t := ⟨hbt.le, le_rfl⟩
  have hwindow : Icc (t - (t - b)) t ⊆ Icc b t := by
    rw [sub_sub_cancel]
  have hbounded : CompleteBoundedCurvatureOn F (Icc (t - (t - b)) t) := by
    simpa only [sub_sub_cancel] using jointSeed_completeBoundedCurvatureOn F
  obtain ⟨hL⟩ := P.m08 M (Icc b t) F t (t - b) ht hd hwindow hbounded
  obtain ⟨hD⟩ := P.m09 M (Icc b t) F t (t - b) ht hd hwindow hbounded hL
  obtain ⟨hV⟩ := P.m10 M (Icc b t) F t (t - b) ht hd hwindow hbounded hL hD
  have htau : 0 < t - b - eta := sub_pos.mpr hetaAge
  have htauMax : t - b - eta < t - b := sub_lt_self _ heta
  obtain ⟨q, _hqmin, hq⟩ := hV.minimum_bound x (t - b - eta) htau htauMax
  obtain ⟨path, hstart, _hend, hmin, hvalue⟩ :=
    hL.reduced_length_attained (t - b - eta) htau htauMax.le x q
  refine ⟨hL, path, hstart, hmin, ?_⟩
  rw [hvalue] at hq
  have hden : 0 < 2 * Real.sqrt (t - b - eta) := by positivity
  have ha := (div_le_iff₀ hden).1 hq
  have hsqrt := Real.sqrt_le_sqrt htauMax.le
  norm_num only [Nat.cast_ofNat] at ha
  nlinarith

end PoincareConjecture.M47
