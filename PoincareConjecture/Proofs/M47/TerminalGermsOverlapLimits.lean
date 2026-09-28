import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.M47

open ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth



theorem terminalGerms_local_coefficient_transition
    (i j : ι)
    (hbound : LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))))
    (Aseq Bseq : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (A B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hA : ∀ x ∈ U i, ∀ v w,
      Tendsto (fun k => Aseq k x v w) atTop (𝓝 (A x v w)))
    (hB : TendstoLocallyUniformlyOn Bseq B atTop (U j))
    (hBcont : ContinuousOn B (U j))
    (hsource : ∀ x ∈ Subtype.val '' overlap (fun i j => D i j) i j,
      ∀ᶠ k in atTop, ∀ v w,
        let f := coordinateRepresentative U hU
          (fun y => Function.invFun (e k j) (e k i y))
        Bseq k (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = Aseq k x v w) :
    let f := coordinateRepresentative U hU (transition (fun i j => D i j) i j)
    ∀ x ∈ Subtype.val '' overlap (fun i j => D i j) i j, ∀ v w,
      B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  apply CoordinateTransition.pullback_eq_of_tendsto (hU j)
    (Aseq := Aseq) (Bseq := Bseq)
    (fseq := fun k => coordinateRepresentative U hU
      (fun x => Function.invFun (e k j) (e k i x)))
    ?_ hB hBcont ?_ ?_ ?_ hsource
  · rintro _ ⟨x, _, rfl⟩ v w
    exact hA x x.property v w
  · rintro _ ⟨x, _, rfl⟩
    rw [coordinateRepresentative_apply]
    exact (transition (fun i j => D i j) i j x).property
  · intro x hx
    exact coordinate_source_transition_tendsto U hU hD L he c hc hlower hopen hconn i j hx
  · intro x hx v
    have hjet := tendsto_coordinate_source_transition_jet U hU hD L he c hc hlower
      hopen hconn hsmooth i j hbound 1 hx
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin n)) (fun _ : Fin 1 => v)
    simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
      (hev.continuous.tendsto _).comp hjet

end PoincareConjecture.M47
