import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.MetricEndRay
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.DistinctEndRays

/-!
# Actual selected rays as finite outward data

The retained ray function at the same completion point supplies every
small source point as an included outer endpoint. The proved distinct
rays give two literal data with different end germs. The selected wall,
source metric and original-cylinder height are preserved.
Source: Morgan--Tian Lemmas 10.16 and 10.18, p. 258;
M28 derivations 135, 153 and 152c.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}

/-- Every actual small source point is the included outer endpoint of
a datum obtained from the SAME retained selected-ray function.
Source: MT Lemma 10.16, p. 258; derivations 135 and 152c. -/
theorem exists_selected_metricEndRay_at_point
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) →
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      (∀ p : U, r p < alpha → 0 < f p) →
      (∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
        gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
        (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
          dist (gamma s) (gamma t) = |s - t|) ∧
        (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
        ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (C.inverse (gamma t)).2) →
      ∀ p : U, r p < alpha / 4 → ∃ P : MetricEndRay E alpha,
        P.length = r p ∧ P.point P.length = p ∧
        ∀ s ∈ Ioc (0 : ℝ) P.length, (3 / 4 : ℝ) ≤ (C.inverse (P.point s)).2 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha houtside
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  dsimp only
  intro hbarrier hproducer p hp
  have hpos : 0 < r p := dist_pos.mpr fun h => houtside ⟨p, h⟩
  have hpalpha : r p < alpha := by linarith only [hp, halpha]
  obtain ⟨gamma, hgamma0, _hgammaIsometry, hgammaMetric, hgammaRadius, hgammaLower⟩ :=
    hproducer p (hbarrier p hpalpha)
  let P : MetricEndRay E alpha :=
    MetricEndRay.ofInward hpos hp gamma hgammaMetric hgammaRadius
  refine ⟨P, rfl, ?_, ?_⟩
  · change gamma (r p - r p) = p
    simpa only [sub_self] using hgamma0
  · intro s hs
    change s ∈ Ioc (0 : ℝ) (r p) at hs
    exact hgammaLower (r p - s)
      ⟨by linarith only [hs.2], by linarith only [hs.1]⟩

/-- The actual distinct selected rays become data with different end
germs, retaining their literal source-point maps and lower heights.
Source: MT Lemma 10.18, p. 258; derivations 153 and 152c. -/
theorem exists_two_distinct_selected_metricEndRay_data
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ), 0 < alpha →
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) →
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      (∀ p : U, r p < alpha → 0 < f p) →
      (∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
        gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
        (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
          dist (gamma s) (gamma t) = |s - t|) ∧
        (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
        ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (C.inverse (gamma t)).2) →
      ∃ P Q : MetricEndRay E alpha,
        ¬MetricEndRay.SameEndGerm P Q ∧
        (∀ s ∈ Ioc (0 : ℝ) P.length, (3 / 4 : ℝ) ≤ (C.inverse (P.point s)).2) ∧
        ∀ s ∈ Ioc (0 : ℝ) Q.length, (3 / 4 : ℝ) ≤ (C.inverse (Q.point s)).2 := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha halpha houtside
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  dsimp only
  intro hbarrier hproducer
  obtain ⟨p, q, gamma, mu, hpPositive, hpSmall, hqLower, hqUpper,
      hgamma, hmu, _hoff, hnear⟩ :=
    exists_two_distinct_selected_metric_end_rays T C U f hfinite
      E alpha halpha houtside hbarrier hproducer
  obtain ⟨_hgamma0, _hgammaIsometry, hgammaMetric, hgammaRadius, hgammaLower⟩ := hgamma
  obtain ⟨_hmu0, _hmuIsometry, hmuMetric, hmuRadius, hmuLower⟩ := hmu
  have hqPositive : 0 < r q := by linarith only [hpPositive, hqLower]
  have hqSmall : r q < alpha / 4 := by linarith only [hpPositive, hpSmall, hqUpper]
  let P : MetricEndRay E alpha :=
    MetricEndRay.ofInward hpPositive hpSmall gamma hgammaMetric hgammaRadius
  let Q : MetricEndRay E alpha :=
    MetricEndRay.ofInward hqPositive hqSmall mu hmuMetric hmuRadius
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · rintro ⟨c, hc, _hcP, _hcQ, hagree⟩
    obtain ⟨s, hs, hdifferent⟩ := hnear c hc
    have heq := hagree ⟨hs.1, hs.2.le.trans (min_le_left _ _)⟩
    change gamma (r p - s) = mu (r q - s) at heq
    exact hdifferent heq
  · intro s hs
    change s ∈ Ioc (0 : ℝ) (r p) at hs
    exact hgammaLower (r p - s)
      ⟨by linarith only [hs.2], by linarith only [hs.1]⟩
  · intro s hs
    change s ∈ Ioc (0 : ℝ) (r q) at hs
    exact hmuLower (r q - s)
      ⟨by linarith only [hs.2], by linarith only [hs.1]⟩

end PoincareMT.M28
