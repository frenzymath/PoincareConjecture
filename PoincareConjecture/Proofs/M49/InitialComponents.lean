import PoincareConjecture.Proofs.M49.CalibratedVolume
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal BigOperators

universe u

namespace PoincareConjecture.M49

theorem ball_subset_connectedComponent {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) (r : ℝ) :
    g.ball x r ⊆ connectedComponent x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  change Manifold.riemannianEDist (𝓡 n) x y < ENNReal.ofReal r at hy
  obtain ⟨γ, hγx, hγy, hγ, _⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  have hc : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  exact hc.subset_connectedComponent ⟨0, by norm_num, hγx⟩ ⟨1, by norm_num, hγy⟩

theorem slice_components_finite (F : SurgeryFlowData.{u}) {t : ℝ}
    (ht : t ∈ F.time_domain) : Finite (ConnectedComponents (F.slice t).carrier) := by
  let : CompactSpace (F.slice t).carrier := isCompact_univ_iff.mp (F.slices_compact t ht)
  let : LocallyConnectedSpace (F.slice t).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (F.slice t).carrier
  infer_instance

theorem initial_component_unit_volume_pos :
    0 < euclideanUnitBallLebesgueVolume.toReal / 2 := by
  apply div_pos _ (by norm_num)
  apply ENNReal.toReal_pos
  · exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 3))
      (by norm_num : (0 : ℝ) < 1)).ne'
  · exact measure_ball_lt_top.ne

theorem initial_component_volume_lower_bound (F : SurgeryFlowData.{u})
    (x : (F.slice 0).carrier) :
    ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal / 2) ≤
      calibratedMetricVolume (F.metric 0) (connectedComponent x) := by
  have hball := (F.initial_normalized x).2 1 (by norm_num) le_rfl
  simp only [one_pow, mul_one] at hball
  exact hball.trans (measure_mono (ball_subset_connectedComponent (F.metric 0) x 1))

theorem initial_components_volume_bound (F : SurgeryFlowData.{u}) :
    (Nat.card (ConnectedComponents (F.slice 0).carrier) : ℝ≥0∞) *
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal / 2) ≤
      calibratedMetricVolume (F.metric 0) univ := by
  classical
  let : Finite (ConnectedComponents (F.slice 0).carrier) :=
    slice_components_finite F F.zero_mem
  let : Fintype (ConnectedComponents (F.slice 0).carrier) := Fintype.ofFinite _
  let p : ConnectedComponents (F.slice 0).carrier → (F.slice 0).carrier :=
    fun c => (ConnectedComponents.surjective_coe c).choose
  have hp (c : ConnectedComponents (F.slice 0).carrier) : ConnectedComponents.mk (p c) = c :=
    (ConnectedComponents.surjective_coe c).choose_spec
  let A : ConnectedComponents (F.slice 0).carrier → Set (F.slice 0).carrier :=
    fun c => {x | ConnectedComponents.mk x = c}
  have hA (c : ConnectedComponents (F.slice 0).carrier) : A c = connectedComponent (p c) := by
    change ConnectedComponents.mk ⁻¹' {c} = _
    simpa only [hp c] using (connectedComponents_preimage_singleton (x := p c))
  have hd : Pairwise (fun c d => Disjoint (A c) (A d)) := by
    intro c d hcd
    exact disjoint_left.mpr (fun _ hx hy => hcd (hx.symm.trans hy))
  calc
    _ = ∑ _c : ConnectedComponents (F.slice 0).carrier,
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal / 2) := by
      simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
    _ ≤ ∑ c : ConnectedComponents (F.slice 0).carrier,
        calibratedMetricVolume (F.metric 0) (A c) := by
      apply Finset.sum_le_sum
      intro c _
      rw [hA]
      exact initial_component_volume_lower_bound F (p c)
    _ ≤ _ := sum_measure_le_measure_univ
      (fun c _ => by rw [hA]; exact isClosed_connectedComponent.measurableSet.nullMeasurableSet)
      (fun _ _ _ _ hcd => (hd hcd).aedisjoint)

theorem exists_uniform_initial_component_bound (V₀ : ℝ≥0∞) (hV₀ : V₀ ≠ ⊤) :
    ∃ n : ℕ, ∀ F : SurgeryFlowData.{u},
      calibratedMetricVolume (F.metric 0) univ ≤ V₀ →
        Nat.card (ConnectedComponents (F.slice 0).carrier) ≤ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (V₀.toReal / (euclideanUnitBallLebesgueVolume.toReal / 2))
  refine ⟨n, fun F hF => ?_⟩
  have hc := ENNReal.toReal_mono hV₀ ((initial_components_volume_bound F).trans hF)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal initial_component_unit_volume_pos.le] at hc
  have hn' := ((le_div_iff₀ initial_component_unit_volume_pos).mpr hc).trans hn
  exact_mod_cast hn'

end PoincareConjecture.M49
