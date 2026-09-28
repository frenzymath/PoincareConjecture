import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing













set_option autoImplicit false

open Set Filter MeasureTheory Bundle Metric
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




theorem m64_lipschitzOn_nhds_of_cut_glue
    (g : RiemannianMetric n M) {f F G : LoopPlane → M}
    {x : LoopPlane} {φ : LoopPlane → ℝ}
    (hφ : Continuous φ)
    (hF : ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      g.edist (F y) (F z) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖)
    (hG : ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      g.edist (G y) (G z) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖)
    (hleft : ∀ y, φ y ≤ φ x → f y = F y)
    (hright : ∀ y, φ x ≤ φ y → f y = G y)
    (hcut : ∀ y, φ y = φ x → F y = G y) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      g.edist (f y) (f z) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  obtain ⟨KF, UF, hUF, hKF⟩ := hF
  obtain ⟨KG, UG, hUG, hKG⟩ := hG
  obtain ⟨rF, hrF, hrFsub⟩ := Metric.mem_nhds_iff.mp hUF
  obtain ⟨rG, hrG, hrGsub⟩ := Metric.mem_nhds_iff.mp hUG
  let r : ℝ := min rF rG / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let S : Set LoopPlane := closedBall x r
  have hSsubF : S ⊆ UF := by
    intro y hy
    apply hrFsub
    apply mem_ball'.mpr
    have hy' : dist x y ≤ r := mem_closedBall'.mp hy
    have hsmall : r < rF := by
      dsimp [r]
      have hmin := min_le_left rF rG
      linarith
    exact hy'.trans_lt hsmall
  have hSsubG : S ⊆ UG := by
    intro y hy
    apply hrGsub
    apply mem_ball'.mpr
    have hy' : dist x y ≤ r := mem_closedBall'.mp hy
    have hsmall : r < rG := by
      dsimp [r]
      have hmin := min_le_right rF rG
      linarith
    exact hy'.trans_lt hsmall
  have hFpiece : LipschitzOnWith KF F (S ∩ {y | φ y ≤ φ x}) := by
    intro y hy z hz
    change g.edist (F y) (F z) ≤ (KF : ℝ≥0∞) * edist y z
    simpa only [edist_dist, dist_eq_norm] using
      hKF y (hSsubF hy.1) z (hSsubF hz.1)
  have hGpiece : LipschitzOnWith KG G (S ∩ {y | φ x ≤ φ y}) := by
    intro y hy z hz
    change g.edist (G y) (G z) ≤ (KG : ℝ≥0∞) * edist y z
    simpa only [edist_dist, dist_eq_norm] using
      hKG y (hSsubG hy.1) z (hSsubG hz.1)
  have hpiece : LipschitzOnWith (max KF KG)
      ({y | φ y ≤ φ x}.piecewise F G) S :=
    M60.lipschitzOnWith_piecewise_of_convex (convex_closedBall x r) φ
      hφ.continuousOn (φ x) hFpiece hGpiece (by
        intro y hy hycut
        exact hcut y hycut)
  refine ⟨max KF KG, ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  intro y hy z hz
  have hyS : y ∈ S := mem_closedBall'.mpr (mem_ball'.mp hy).le
  have hzS : z ∈ S := mem_closedBall'.mpr (mem_ball'.mp hz).le
  have hfy : f y = ({w | φ w ≤ φ x}.piecewise F G) y := by
    by_cases hφy : φ y ≤ φ x
    · simpa only [piecewise, mem_ofPred_eq, if_pos hφy] using hleft y hφy
    · simpa only [piecewise, mem_ofPred_eq, if_neg hφy] using
        hright y (le_of_not_ge hφy)
  have hfz : f z = ({w | φ w ≤ φ x}.piecewise F G) z := by
    by_cases hφz : φ z ≤ φ x
    · simpa only [piecewise, mem_ofPred_eq, if_pos hφz] using hleft z hφz
    · simpa only [piecewise, mem_ofPred_eq, if_neg hφz] using
        hright z (le_of_not_ge hφz)
  rw [hfy, hfz]
  have hp := hpiece hyS hzS
  change g.edist (({w | φ w ≤ φ x}.piecewise F G) y)
      (({w | φ w ≤ φ x}.piecewise F G) z) ≤
    ((max KF KG : ℝ≥0) : ℝ≥0∞) * edist y z at hp
  simpa only [edist_dist, dist_eq_norm] using hp

end PoincareConjecture
