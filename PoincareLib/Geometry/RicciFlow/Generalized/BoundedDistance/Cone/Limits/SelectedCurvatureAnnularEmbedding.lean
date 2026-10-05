import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedAnnularApproximation
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Curvature.CurvatureScaleAnnularLimit

/-!
# Actual curvature-scale embeddings into the completed chord annulus

The same selected geometry supplies the annular maps. Actual original-U
source distances then give an extended-distance-preserving map for the
terminal metric on the retained parameter points, with a closed radial
buffer. The parameter type receives no Riemannian or Euclidean metric
instance in this adapter.
Source: Morgan--Tian Sections 10.5-10.6, pp. 263-265;
M28 derivations 158, 159 and 159b.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M28

/-- The complete actual annular-embedding statement, with all three
metric bindings retained literally. Naming the proposition separates
their elaboration from theorem-header closure.
Source: Sections 10.5-10.6; derivations 159b and 159c. -/
def SelectedCurvatureAnnularEmbeddingStatement
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {X : Set M}
    {S : Type*}
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (referenceDistance : S → S → ℝ≥0∞) : Prop :=
    letI sourceMetric : MetricSpace U := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      E ∉ range ((↑) : U → UniformSpace.Completion U) →
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      (∀ p : U, r p < alpha → 0 < f p) →
      (∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
        gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
        (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
          dist (gamma s) (gamma t) = |s - t|) ∧
        (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
        ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2) →
      ∀ chordMetric : PseudoMetricSpace (MetricEndRay E alpha),
        letI := chordMetric
        CompactSpace (UniformSpace.Completion (MetricEndRay E alpha)) →
        (∀ P Q : MetricEndRay E alpha,
          ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
            chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2) →
        (∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
          (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (chordConeDistance r s (dist P Q)))) →
        ∀ (x : ℕ → S → U) (q : ℕ → U) (R : ℕ → ℝ)
          (hRpos : ∀ i, 0 < R i) (hRtop : Tendsto R atTop atTop)
          (a m : ℝ) (hm : 0 < m) (ham : a ≤ m)
          (hcenter : Tendsto (fun i => Real.sqrt (R i) * r (q i)) atTop (𝓝 m))
          (hshort : ∀ᶠ i in atTop, ∀ u : S,
            Real.sqrt (R i) * dist (x i u) (q i) ≤ 3 * a / 64)
          (hreferenceFinite : ∀ u v : S, referenceDistance u v ≠ ⊤)
          (hsource : ∀ u v : S, Tendsto
            (fun i => Real.sqrt (R i) * dist (x i u) (x i v))
            atTop (𝓝 (referenceDistance u v).toReal))
          (htriangle : ∀ z w v : UniformSpace.Completion (MetricEndRay E alpha),
            ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
              chordConeDistance r t (dist z v) ≤
                chordConeDistance r s (dist z w) + chordConeDistance s t (dist w v)),
          letI := chordConeAnnulusMetric (half_pos hm)
            ((half_le_self hm.le).trans
              (le_mul_of_one_le_left hm.le (by norm_num : (1 : ℝ) ≤ 2))) htriangle
          ∃ j : S → ChordConeAnnulus
              (UniformSpace.Completion (MetricEndRay E alpha)) (m / 2) (2 * m),
            (∀ u v : S, edist (j u) (j v) = referenceDistance u v) ∧
            ∀ u : S, ((j u).2 : ℝ) ∈ Icc (3 * m / 4) (5 * m / 4)

/-- Calling the actual selected annular-map producer and the common
compact-limit theorem preserves the literal finite reference distances
and an interior radial buffer in the same original open-region metric.
Source: Sections 10.5-10.6; derivations 159b and 159c. -/
theorem exists_selected_curvatureScale_annular_embedding
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {X : Set M} {S : Type*}
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
    (referenceDistance : S → S → ℝ≥0∞) :
    SelectedCurvatureAnnularEmbeddingStatement T A U f hfinite referenceDistance := by
  let sourceMetric : MetricSpace U := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha houtside
  dsimp only
  intro hbarrier hproducer chordMetric
  let := chordMetric
  intro hcompact hupper hscaled x q R hRpos hRtop a m hm ham hcenter hshort
    hreferenceFinite hsource htriangle
  let := hcompact
  have hab : m / 2 ≤ 2 * m := by linarith only [hm]
  let := chordConeAnnulusMetric (half_pos hm) hab htriangle
  obtain ⟨F, hFradius, hFdistortion⟩ :=
    exists_selected_annular_approximation_maps T A U f hfinite
      E alpha halpha houtside hbarrier hproducer chordMetric hcompact hupper hscaled
        (m / 2) (2 * m) (half_pos hm) hab htriangle
  obtain ⟨j, _hcommon, hjdist, hjradius⟩ :=
    exists_curvatureScale_annular_limit (S := S) (X := U)
      (L := UniformSpace.Completion (MetricEndRay E alpha))
      E x q R hRpos hRtop (a := a) (m := m) hm ham hcenter hshort
      referenceDistance hreferenceFinite hsource htriangle
        F hFradius hFdistortion
  exact ⟨j, hjdist, hjradius⟩

end PoincareMT.M28
