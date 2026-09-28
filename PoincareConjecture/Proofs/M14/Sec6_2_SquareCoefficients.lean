import PoincareConjecture.Proofs.M14.Sec6_2_PotentialCoefficient
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_SquareEnergy










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M14

section Metric

variable {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
  (g : ℝ → RiemannianMetric n U)



noncomputable def squareMetricCoefficient (T : ℝ) (x : U)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  Proofs.M11.ordinaryChartMetric g x (T - z.1 ^ 2, z.2)



theorem squareMetricCoefficient_apply (T : ℝ) (x y : U) (s : ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    squareMetricCoefficient U g T x (s, y.val) v w = (g (T - s ^ 2)).inner y v w :=
  ordinaryChartMetric_openSubset_apply U g x y (T - s ^ 2) v w



theorem squareMetricCoefficient_contDiffOn {K J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g K) (T : ℝ) (x : U)
    (htime : ∀ s ∈ J, T - s ^ 2 ∈ K) :
    ContDiffOn ℝ ∞ (squareMetricCoefficient U g T x) (J ×ˢ (U : Set _)) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hm := Proofs.M11.ordinaryChartMetric_smooth g K hg x
  apply hm.comp ((contDiffOn_const.sub (contDiffOn_fst.pow 2)).prodMk contDiffOn_snd)
  intro z hz
  refine ⟨htime z.1 hz.1, ?_⟩
  change z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).target
  rw [U.chartAt_target_eq]
  exact hz.2



theorem squareMetricCoefficient_pos (T : ℝ) (x : U) (s : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < squareMetricCoefficient U g T x (s, y) v v := by
  rw [show y = (⟨y, hy⟩ : U).val from rfl, squareMetricCoefficient_apply]
  exact (g (T - s ^ 2)).pos _ v hv



theorem backwardMetricCoefficient_square (T : ℝ) (x : U) {s : ℝ} (hs : 0 ≤ s)
    (z : EuclideanSpace ℝ (Fin n)) :
    backwardMetricCoefficient U g T x (s ^ 2, z) =
      (2 * s) • squareMetricCoefficient U g T x (s, z) := by
  simp only [backwardMetricCoefficient, squareMetricCoefficient, Real.sqrt_sq hs]

end Metric

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
  (x : G.gaugeCover.spatial b)



noncomputable def squarePotentialCoefficient (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 * z.1 ^ 2 * horizontalScalarCurvature G.leafwise
    ((G.gaugeCover.cylinder b).toSpacetime
      (θ z.1, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm z.2))



theorem squarePotentialCoefficient_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {J : Set ℝ}
    (hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ J) :
    ContDiffOn ℝ ∞ (squarePotentialCoefficient b θ x)
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
  exact (contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul hscalar.contDiffOn



theorem squarePotentialCoefficient_eq_backward {s : ℝ} (hs : 0 ≤ s)
    (z : EuclideanSpace ℝ (Fin n)) :
    squarePotentialCoefficient b (fun r => θ (r ^ 2)) x (s, z) =
      (2 * s) * backwardPotentialCoefficient b θ x (s ^ 2, z) := by
  simp only [squarePotentialCoefficient, backwardPotentialCoefficient, Real.sqrt_sq hs]
  ring




theorem squareGauge_coefficients_contDiffOn
    {T τ₁ τ₂ : ℝ} {q r : G.Point} (p : M14BackwardPath G T τ₁ τ₂ q r)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set G.Point}
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {C : Set ℝ} (hC : C ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hsrc : ∀ s ∈ C, p.curve (s ^ 2) ∈ U) :
    ContDiffOn ℝ ∞
      (squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x)
      (C ×ˢ (G.gaugeCover.spatial b : Set _)) ∧
    ContDiffOn ℝ ∞
      (squarePotentialCoefficient b (fun s => (lift (p.curve (s ^ 2))).1) x)
      (C ×ˢ (G.gaugeCover.spatial b : Set _)) := by
  have hclock (s : ℝ) (hs : s ∈ C) : (lift (p.curve (s ^ 2))).1.val = T - s ^ 2 :=
    gaugeLift_time_eq p b lift hright (squarePath_parameter_mem p (hC hs)) (hsrc s hs)
  have hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞
      (fun s => (lift (p.curve (s ^ 2))).1) C := by
    apply intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
      (G.timeIntervals.interval (G.gaugeCover.interval b))
    have hc : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => T - s ^ 2) C :=
      (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
    exact hc.congr hclock
  refine ⟨squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial b)
    (G.gaugeCover.metric b).metric (G.gaugeCover.metric b).smooth T x ?_,
    squarePotentialCoefficient_contDiffOn b _ x hM12 hθ⟩
  intro s hs
  rw [← hclock s hs]
  exact (lift (p.curve (s ^ 2))).1.property

end PoincareConjecture.M14
