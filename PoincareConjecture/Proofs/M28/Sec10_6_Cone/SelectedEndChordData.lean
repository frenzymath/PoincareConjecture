import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedCylinderMetricRays
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedSphereRadiusBarrier
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedChordCompactness
import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayEndpoint
import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayConeTriangle
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.ChordConeAnnulus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}

structure SelectedEndChordData
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) where

  endPoint : letI := intrinsicOpenMetricSpace g U hfinite
    UniformSpace.Completion U

  endPoint_missing : letI := intrinsicOpenMetricSpace g U hfinite
    endPoint ∉ range ((↑) : U → UniformSpace.Completion U)

  alpha : ℝ

  alpha_pos : 0 < alpha

  wall : M → ℝ

  radius_continuous : letI := intrinsicOpenMetricSpace g U hfinite
    Continuous (fun x : U => dist (x : UniformSpace.Completion U) endPoint)

  radius_pos : letI := intrinsicOpenMetricSpace g U hfinite
    ∀ x : U, 0 < dist (x : UniformSpace.Completion U) endPoint

  tail_radius : letI := intrinsicOpenMetricSpace g U hfinite
    ∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
      ∀ x : U, c < (A.inverse x).2 →
        dist (x : UniformSpace.Completion U) endPoint < eta

  radius_barrier : letI := intrinsicOpenMetricSpace g U hfinite
    ∀ x : U, dist (x : UniformSpace.Completion U) endPoint < alpha → 0 < wall x

  segments : letI := intrinsicOpenMetricSpace g U hfinite
    ∀ p q : U, 0 < wall p → 0 < wall q →
      ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
        (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          (intrinsicOpenMetric g U).edist (mu s) (mu t) =
            ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q

  inward_rays : letI := intrinsicOpenMetricSpace g U hfinite
    let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) endPoint
    ∀ p : U, 0 < wall p → ∃ gamma : ℝ → U,
      gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
      (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
        dist (gamma s) (gamma t) = |s - t|) ∧
      (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
      ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2

  chordMetric : letI := intrinsicOpenMetricSpace g U hfinite
    PseudoMetricSpace (MetricEndRay endPoint alpha)

  chord_compact : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    CompactSpace (UniformSpace.Completion (MetricEndRay endPoint alpha))

  chord_le_two : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, dist P Q ≤ 2

  joint_chord_limit : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, Tendsto
      (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (dist P Q ^ 2))

  equal_radius_limit : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, Tendsto
      (fun h : ℝ => dist (P.point h) (Q.point h) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist P Q))

  scaled_distance_limit : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
      (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (chordConeDistance r s (dist P Q)))

  strict_chord_bound : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, ∀ s ∈ Ioo (0 : ℝ) P.length,
      ∀ t ∈ Ioo (0 : ℝ) Q.length,
        chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2

  endpoint_distance_bound : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha, ∀ s ∈ Ioc (0 : ℝ) P.length,
      ∀ t ∈ Ioc (0 : ℝ) Q.length,
        dist (P.point s) (Q.point t) ≤ chordConeDistance s t (dist P Q)

  zero_iff_sameEndGerm : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ P Q : MetricEndRay endPoint alpha,
      dist P Q = 0 ↔ MetricEndRay.SameEndGerm P Q

  completed_triangle : letI := intrinsicOpenMetricSpace g U hfinite
    letI := chordMetric
    ∀ x y z : UniformSpace.Completion (MetricEndRay endPoint alpha),
      ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
        chordConeDistance r t (dist x z) ≤
          chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z)

theorem exists_selected_end_chord_data
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (D0 : LeviCivitaData g) (hR : ContinuousOn D0.scalarCurvature T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D0.scalarCurvature y ≤ 2 * D0.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D0.scalarCurvature x)
    {B : ℝ} (hB : 0 < B) (hdiam : intrinsicDiameter g (U : Set M) ≤ ENNReal.ofReal B)
    (hsmall : T.epsilon ≤ neckShorteningEpsilon)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (DU : LeviCivitaData (intrinsicOpenMetric g U))
    (hsec : DU.NonnegativeSectionalCurvature) :
    Nonempty (SelectedEndChordData T A U hfinite) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  have hpreconnected : IsPreconnected (U : Set M) := by
    rw [hU]
    exact A.isPreconnected_tail true (by norm_num) (by norm_num)
  let : PreconnectedSpace U := Subtype.preconnectedSpace hpreconnected
  obtain ⟨E, houtside, hcontinuous, hpositive, _htriangle, htail, _hsequences,
      i, _hi, f, b, _hbhalf, hb1, hf, hzero, hNU, hhigh, hsegments, hrays⟩ :=
    exists_selected_cylinder_metric_rays T A U hU hA D0 hR hratio hdiverge
      hB hdiam hsmall hfinite
  obtain ⟨alpha, halpha, _hminimum, _hsphere, _hcross, _hnonpositive, hbarrier⟩ :=
    exists_selected_sphere_radius_barrier T A U hU i f hf hzero hNU (b := b) hb1 hhigh
      hfinite E houtside htail
  obtain ⟨m, hm⟩ := exists_compact_selected_end_chord_link T A U hU hA
    D0.scalarCurvature hR hratio hdiverge f hfinite DU hsec
      E alpha houtside halpha htail hbarrier hsegments
  let := m
  obtain ⟨_htotally, hcompact, hdiameter, hjoint, hequal, hscaled, hupper, hgerm⟩ := hm
  have hsourceTriangle := metricEndRay_chordConeTriangle hscaled
  have hcompleted := chordConeTriangle_completion hsourceTriangle
  exact ⟨{
    endPoint := E
    endPoint_missing := houtside
    alpha := alpha
    alpha_pos := halpha
    wall := f
    radius_continuous := hcontinuous
    radius_pos := hpositive
    tail_radius := htail
    radius_barrier := hbarrier
    segments := hsegments
    inward_rays := hrays
    chordMetric := m
    chord_compact := hcompact
    chord_le_two := hdiameter
    joint_chord_limit := hjoint
    equal_radius_limit := hequal
    scaled_distance_limit := hscaled
    strict_chord_bound := hupper
    endpoint_distance_bound := fun P Q s hs t ht =>
      P.dist_le_chordConeDistance Q (hupper P Q) s hs t ht
    zero_iff_sameEndGerm := hgerm
    completed_triangle := hcompleted }⟩

end PoincareConjecture.M28
