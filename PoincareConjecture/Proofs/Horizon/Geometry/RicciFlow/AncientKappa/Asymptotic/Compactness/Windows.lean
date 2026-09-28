import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

def compactnessLower (j : ℕ) : ℝ := -((j : ℝ) + 2)

noncomputable def compactnessUpper (j : ℕ) : ℝ := -((j : ℝ) + 2)⁻¹

theorem compactnessLower_le (j : ℕ) : compactnessLower j ≤ -2 := by
  unfold compactnessLower
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

theorem compactnessUpper_neg (j : ℕ) : compactnessUpper j < 0 := by
  exact neg_neg_of_pos (inv_pos.mpr (by positivity))

theorem compactnessUpper_base (j : ℕ) : -1 < compactnessUpper j := by
  unfold compactnessUpper
  exact neg_lt_neg ((inv_lt_one₀ (by positivity : 0 < (j : ℝ) + 2)).2 (by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith))

theorem timeWindow_subset_compactnessWindow (j : ℕ) :
    ancientM18TimeWindow j ⊆ Ioo (compactnessLower j) (compactnessUpper j) := by
  intro t ht
  constructor
  · change -((j : ℝ) + 2) < t
    have := ht.1
    change -((j : ℝ) + 1) ≤ t at this
    linarith
  · apply lt_of_le_of_lt ht.2
    apply neg_lt_neg
    exact (inv_lt_inv₀ (by positivity : 0 < (j : ℝ) + 2)
      (by positivity : 0 < (j : ℝ) + 1)).2 (by linarith)

abbrev sourceCarrier : FlowCarrier n where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance
  connected := isConnected_univ

def shiftedWindowFlow (S : AncientRescalingSequence K) (j k : ℕ) :
    RicciFlow n M (Ioo (compactnessLower j + 1) (compactnessUpper j + 1)) :=
  (S.rescaling k).flow.translate (-1)
    (by
      rintro t ⟨s, hs, rfl⟩
      have := compactnessUpper_neg j
      change s + -1 < 0
      linarith [hs.2])
    ordConnected_Ioo
    (by
      refine ⟨0, ⟨?_, ?_⟩, (compactnessUpper j + 1) / 2, ⟨?_, ?_⟩, ?_⟩
      all_goals have := compactnessLower_le j
      all_goals have := compactnessUpper_base j
      all_goals linarith)

noncomputable def basedWindow (S : AncientRescalingSequence K) (j k : ℕ) :
    BasedFlow n (compactnessLower j + 1) (compactnessUpper j + 1)
      (sourceCarrier (M := M)) where
  base := S.base k
  flow := S.shiftedWindowFlow j k
  volumeMeasure := (sourceCarrier (M := M)).metricHausdorffVolume
    ((S.shiftedWindowFlow j k).metric 0)
  spacetimeVectorField := fun _ _ ↦ (1, 0)
  spacetimeVectorField_time := fun _ _ ↦ rfl
  spacetimeVectorField_spatial_zero := fun _ _ ↦ rfl

noncomputable def windowSequence (S : AncientRescalingSequence K) (j : ℕ) :
    PointedFlowSequence n (compactnessLower j + 1) (compactnessUpper j + 1) where
  carrier := fun _ ↦ sourceCarrier (M := M)
  flow := S.basedWindow j

theorem basedWindow_volumeCompatible (S : AncientRescalingSequence K) (j k : ℕ) :
    (S.basedWindow j k).volumeCompatible := rfl

theorem basedWindow_zeroBall (S : AncientRescalingSequence K) (j k : ℕ) (r : ℝ) :
    (S.basedWindow j k).zeroBall r =
      ((S.rescaling k).flow.metric (-1)).ball (S.base k) r := by
  simp only [BasedFlow.zeroBall, basedWindow, shiftedWindowFlow,
    RicciFlow.translate, FlowCarrier.metricBall, zero_add]

theorem basedWindow_ballAt (S : AncientRescalingSequence K) (j k : ℕ) (t r : ℝ) :
    (S.basedWindow j k).ballAt t r =
      ((S.rescaling k).flow.metric (t - 1)).ball (S.base k) r := rfl

theorem basedWindow_zeroBall_compact (S : AncientRescalingSequence K) (j k : ℕ)
    (r : ℝ) : IsCompact (closure ((S.basedWindow j k).zeroBall r)) := by
  rw [S.basedWindow_zeroBall]
  exact ((S.rescaling k).flow.metric (-1)).isCompact_closure_ball_of_metricComplete
    ((S.rescaling k).complete (-1) (by norm_num)) (S.base k) r

end PoincareConjecture.AncientRescalingSequence
