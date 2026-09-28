import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRay
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.MissingEndComparison
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.ChordDefectLimits

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem exists_selected_end_ray_chord_limits
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) [PreconnectedSpace U]
    (hU : (U : Set M) = C.tail true (1 / 2)) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (D : LeviCivitaData (intrinsicOpenMetric g U))
    (hsec : D.NonnegativeSectionalCurvature) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (C.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta) →
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (C.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∃ K : MetricEndRay E alpha → MetricEndRay E alpha → ℝ,
        (∀ P Q : MetricEndRay E alpha, K P Q ∈ Icc (0 : ℝ) 4) ∧
        (∀ P Q : MetricEndRay E alpha,
          ∀ S ∈ Ioo (0 : ℝ) P.length, ∀ V ∈ Ioo (0 : ℝ) Q.length,
          chordDefect (fun s t => dist (P.point s) (Q.point t)) S V ≤ K P Q) ∧
        ∀ P Q : MetricEndRay E alpha, Tendsto
          (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (K P Q)) := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha htail hbarrier hsegments
  have hcomparison (P Q : MetricEndRay E alpha) {S V : ℝ}
      (hS : 0 < S) (hSP : S < P.length) (hV : 0 < V) (hVQ : V < Q.length)
      (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) S)
      (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) V) :
      dist (P.point s) (Q.point t) ^ 2 ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((S ^ 2 + V ^ 2 - dist (P.point S) (Q.point V) ^ 2) /
          (2 * S * V)) := by
    have h := corresponding_side_lower_at_selected_end T C U hU f hfinite D hsec
      E alpha halpha htail hbarrier hsegments
      P.inward_metric Q.inward_metric P.inward_radius Q.inward_radius
      hS hSP (hSP.trans P.length_lt) hV hVQ (hVQ.trans Q.length_lt) s hs t ht
    simpa only [MetricEndRay.inward, sub_sub_cancel] using h
  have hexists (P Q : MetricEndRay E alpha) :
      ∃ k : ℝ, k ∈ Icc (0 : ℝ) 4 ∧
        (∀ s ∈ Ioc (0 : ℝ) (P.length / 2),
          ∀ t ∈ Ioc (0 : ℝ) (Q.length / 2),
            chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ k) ∧
        Tendsto
          (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
          ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 k) := by
    apply exists_chordDefect_limit_of_corresponding_side_lower
      (half_pos P.length_pos) (half_pos Q.length_pos)
    · intro s hs t ht
      exact P.completion_triangle Q s
        ⟨hs.1, hs.2.trans (half_le_self P.length_pos.le)⟩ t
        ⟨ht.1, ht.2.trans (half_le_self Q.length_pos.le)⟩
    · intro S hS V hV s hs t ht
      exact hcomparison P Q hS.1 (hS.2.trans_lt (half_lt_self P.length_pos))
        hV.1 (hV.2.trans_lt (half_lt_self Q.length_pos)) s hs t ht
  choose K hK _hsmall hlimit using hexists
  refine ⟨K, hK, ?_, hlimit⟩
  intro P Q S hS V hV
  exact chordDefect_le_joint_limit_of_corresponding_side_lower hS.1 hV.1
    (hlimit P Q) (hcomparison P Q hS.1 hS.2 hV.1 hV.2)

end PoincareConjecture.M28
