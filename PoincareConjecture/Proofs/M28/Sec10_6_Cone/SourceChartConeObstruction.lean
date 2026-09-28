import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedEndChordData
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedCurvatureAnnularEmbedding
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.LocalConeObstruction











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}

set_option maxHeartbeats 12800000 in


def SelectedEndSourceChartObstructionStatement
    (P0 : RicciFlowCurvatureTheory.{0})
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (S : SelectedEndChordData T A U hfinite)
    {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (ham : a ≤ m) : Prop :=
    let _ := P0
    let _ := hm
    let _ := ham
    let V : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
    let K : Set E3 := Metric.closedBall 0 (a / 64)
    let k : K → V := fun z =>
      ⟨z, Metric.closedBall_subset_ball (by linarith only [ha]) z.property⟩
    letI : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ Fc : RicciFlow 3 V (Icc (-(1 / 8 : ℝ)) 0),
      (∀ t ∈ Icc (-(1 / 8 : ℝ)) 0, ∀ z : V,
        (Fc.connection t).NonnegativeCurvatureOperator z) →
      (Fc.connection 0).scalarCurvature ⟨0, Metric.mem_ball_self ha⟩ = 1 →
      letI := intrinsicOpenMetricSpace g U hfinite
      ∀ (q : ℕ → U) (R : ℕ → ℝ), (∀ i, 0 < R i) →
        Tendsto R atTop atTop →
        Tendsto (fun i => Real.sqrt (R i) *
          dist (q i : UniformSpace.Completion U) S.endPoint) atTop (𝓝 m) →
        ∀ x : ℕ → K → U,
          (∀ z w : K, (Fc.metric 0).edist (k z) (k w) ≠ ⊤) →
          (∀ z w : K, Tendsto
            (fun i => Real.sqrt (R i) * dist (x i z) (x i w))
            atTop (𝓝 ((Fc.metric 0).edist (k z) (k w)).toReal)) →
          (∀ᶠ i in atTop, ∀ z : K,
            Real.sqrt (R i) * dist (x i z) (q i) ≤ 3 * a / 64) → False

set_option maxHeartbeats 12800000 in






theorem no_selected_end_source_chart_limit
    (P0 : RicciFlowCurvatureTheory.{0})
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (S : SelectedEndChordData T A U hfinite)
    {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (ham : a ≤ m) :
    SelectedEndSourceChartObstructionStatement P0 T A U hfinite S ha hm ham := by
  dsimp only [SelectedEndSourceChartObstructionStatement]
  let V : TopologicalSpace.Opens E3 := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
  let K : Set E3 := Metric.closedBall 0 (a / 64)
  let k : K → V := fun z =>
    ⟨z, Metric.closedBall_subset_ball (by linarith only [ha]) z.property⟩
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro Fc hoperator hscalar
  let := intrinsicOpenMetricSpace g U hfinite
  intro q R hRpos hRtop hcenter x hreferenceFinite hsource hshort
  let := S.chordMetric
  have hab : m / 2 ≤ 2 * m := by linarith only [hm]
  let := chordConeAnnulusMetric (half_pos hm) hab S.completed_triangle
  obtain ⟨j, hjmetric, hjradius⟩ :=
    exists_selected_curvatureScale_annular_embedding T A U S.wall hfinite
      (fun u v => (Fc.metric 0).edist (k u) (k v)) S.endPoint S.alpha
      S.alpha_pos S.endPoint_missing
        S.radius_barrier S.inward_rays S.chordMetric S.chord_compact
        S.strict_chord_bound S.scaled_distance_limit
        x q R hRpos hRtop a m hm ham hcenter hshort hreferenceFinite hsource
        S.completed_triangle
  let K' : Set V := {z | (z : E3) ∈ K}
  let j' : K' → ChordConeAnnulus
      (UniformSpace.Completion (MetricEndRay S.endPoint S.alpha)) (m / 2) (2 * m) :=
    fun z => j ⟨z.val.val, z.property⟩
  have hjmetric' : ∀ z w : K',
      edist (j' z) (j' w) = (Fc.metric 0).edist (z : V) (w : V) := by
    intro z w
    exact hjmetric ⟨z.val.val, z.property⟩ ⟨w.val.val, w.property⟩
  have hjmargin : ∀ z : K', ((j' z).2 : ℝ) ∈ Ioo (m / 2) (2 * m) := by
    intro z
    have hz := hjradius ⟨z.val.val, z.property⟩
    exact ⟨(by linarith only [hm] : m / 2 < 3 * m / 4).trans_le hz.1,
      hz.2.trans_lt (by linarith only [hm] : 5 * m / 4 < 2 * m)⟩
  let V' : TopologicalSpace.Opens V :=
    ⟨(Subtype.val : V → E3) ⁻¹' Metric.ball 0 (a / 128),
      Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hVK : (V' : Set V) ⊆ K' := by
    intro z hz
    change (z : E3) ∈ Metric.closedBall 0 (a / 64)
    have hz' : dist (z : E3) 0 < a / 128 := hz
    exact Metric.mem_closedBall.mpr (by linarith only [hz', ha])
  let p : V' :=
    ⟨⟨0, Metric.mem_ball_self ha⟩, Metric.mem_ball_self (by positivity)⟩
  have hscalarPos : 0 < (Fc.connection 0).scalarCurvature (p : V) := by
    change 0 < (Fc.connection 0).scalarCurvature ⟨0, Metric.mem_ball_self ha⟩
    rw [hscalar]
    norm_num
  exact no_positive_terminal_scalar_of_chord_annulus_embedding P0
    (by norm_num : -(1 / 8 : ℝ) < 0) Fc hoperator
      (half_pos hm) hab S.completed_triangle K' V' hVK j'
        hjmetric' hjmargin p hscalarPos

end PoincareConjecture.M28
