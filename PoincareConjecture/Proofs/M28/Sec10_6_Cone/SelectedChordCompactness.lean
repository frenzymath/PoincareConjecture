import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayChord
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.SelectedEndRayChordLimits
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedChordPacking












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}





theorem exists_compact_selected_end_chord_link
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) [PreconnectedSpace U]
    (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < R x)
    (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (D : LeviCivitaData (intrinsicOpenMetric g U))
    (hsec : D.NonnegativeSectionalCurvature) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
      E ∉ range ((↑) : U → UniformSpace.Completion U) → 0 < alpha →
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (A.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta) →
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∃ m : PseudoMetricSpace (MetricEndRay E alpha),
        letI := m
        TotallyBounded (univ : Set (MetricEndRay E alpha)) ∧
        CompactSpace (UniformSpace.Completion (MetricEndRay E alpha)) ∧
        (∀ P Q : MetricEndRay E alpha, dist P Q ≤ 2) ∧
        (∀ P Q : MetricEndRay E alpha, Tendsto
          (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (dist P Q ^ 2))) ∧
        (∀ P Q : MetricEndRay E alpha, Tendsto
          (fun h : ℝ => dist (P.point h) (Q.point h) / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (dist P Q))) ∧
        (∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
          (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Real.sqrt ((r - s) ^ 2 + r * s * dist P Q ^ 2)))) ∧
        (∀ P Q : MetricEndRay E alpha, ∀ s ∈ Ioo (0 : ℝ) P.length,
          ∀ t ∈ Ioo (0 : ℝ) Q.length,
            chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2) ∧
        ∀ P Q : MetricEndRay E alpha,
          dist P Q = 0 ↔ MetricEndRay.SameEndGerm P Q := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha houtside halpha htail hbarrier hsegments
  obtain ⟨K, hK, hupper, hlimit⟩ := exists_selected_end_ray_chord_limits
    T A U hU f hfinite D hsec E alpha halpha htail hbarrier hsegments
  obtain ⟨m, hm⟩ := exists_metricEndRay_chord_pseudometric E alpha K hK hupper hlimit
  refine ⟨m, ?_⟩
  let := m
  obtain ⟨hdiam, hjoint, hequal, hfixed, hstrict, hzero⟩ := hm
  have htotally := totallyBounded_selected_end_ray_chord T A U hU hA R hR hratio
    hdiverge f hfinite E alpha houtside halpha htail hbarrier hsegments m hjoint
  exact ⟨htotally, UniformSpace.Completion.compactSpace_of_totallyBounded_univ htotally,
    hdiam, hjoint, hequal, hfixed, hstrict, hzero⟩

end PoincareConjecture.M28
