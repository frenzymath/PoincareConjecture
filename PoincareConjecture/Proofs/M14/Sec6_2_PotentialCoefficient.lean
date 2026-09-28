import PoincareConjecture.Proofs.M14.Sec6_2_SpatialMetricCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCurve
import PoincareConjecture.Statements.M12GeneralizedEquation

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
  (x : G.gaugeCover.spatial b)

noncomputable def backwardPotentialCoefficient (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt z.1 * horizontalScalarCurvature G.leafwise
    ((G.gaugeCover.cylinder b).toSpacetime
      (θ z.1, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm z.2))

theorem backwardPotentialCoefficient_apply (t : ℝ) (y : G.gaugeCover.spatial b) :
    backwardPotentialCoefficient b θ x (t, y.val) = Real.sqrt t *
      horizontalScalarCurvature G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (θ t, y)) := by
  simp only [backwardPotentialCoefficient, (G.gaugeCover.spatial b).chartAt_symm_apply_val]

theorem backwardPotentialCoefficient_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {J : Set ℝ}
    (hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ J)
    (hpos : ∀ t ∈ J, 0 < t) :
    ContDiffOn ℝ ∞ (backwardPotentialCoefficient b θ x)
      (J ×ˢ (G.gaugeCover.spatial b : Set _)) := by
  have ht : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡∂ 1) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => θ z.1)
      (J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))) := by
    have hf : ContDiff ℝ ∞ (Prod.fst : ℝ × EuclideanSpace ℝ (Fin n) → ℝ) := contDiff_fst
    exact hθ.comp hf.contMDiff.contMDiffOn (fun _ hz => hz.1)
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
      (G.gaugeCover.spatial b : Set _) := by
    simpa only [(G.gaugeCover.spatial b).chartAt_target_eq] using
      (contMDiffOn_chart_symm (I := 𝓡 n) (x := x))
  have hs : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (chartAt (EuclideanSpace ℝ (Fin n)) x).symm z.2)
      (J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))) := by
    have hf : ContDiff ℝ ∞
        (Prod.snd : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := contDiff_snd
    exact hc.comp hf.contMDiff.contMDiffOn (fun _ hz => hz.2)
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := (H.scalar_smooth.comp (G.gaugeCover.cylinder b).smooth).comp_contMDiffOn
    (ht.prodMk hs)
  exact (contDiffOn_fst.sqrt (fun z hz => (hpos z.1 hz.1).ne')).mul hscalar.contDiffOn

theorem gaugeCurve_quadraticDensity (u : ℝ → G.gaugeCover.spatial b) {T s : ℝ}
    (hθ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s)
    (hu : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) u s)
    (hclock : (θ s).val = T - s) :
    M14RawLIntegrand G (fun t => (G.gaugeCover.cylinder b).toSpacetime (θ t, u t))
      (projectedCurveVelocity G
        (fun t => (G.gaugeCover.cylinder b).toSpacetime (θ t, u t))) s =
      backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x
        (s, (u s).val) (deriv (fun t => (u t).val) s) (deriv (fun t => (u t).val) s) / 2 +
      backwardPotentialCoefficient b θ x (s, (u s).val) := by
  rw [gaugeCurve_rawLIntegrand b θ u hθ hu, backwardMetricCoefficient_apply,
    backwardPotentialCoefficient_apply, hclock]
  ring

end PoincareConjecture.M14
