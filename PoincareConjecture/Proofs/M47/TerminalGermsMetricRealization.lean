import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CoordinateFamily











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47



theorem terminalGerms_realize_chart_metric
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)] (i : ι)
    {J : Set ℝ} {t0 : ℝ} (ht0 : t0 ∈ J)
    (Bseq : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U i))
    (hsymm : ∀ k, ∀ t ∈ J, ∀ x ∈ U i, ∀ v w,
      Bseq k (t, x) v w = Bseq k (t, x) w v)
    (hconv : ∀ t ∈ J, ∀ x ∈ U i, ∀ v w,
      Tendsto (fun k => Bseq k (t, x) v w) atTop (𝓝 (B (t, x) v w)))
    (hlower : ∀ t ∈ J, ∀ x ∈ U i, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ v, c * ‖v‖ ^ 2 ≤ Bseq k (t, x) v v)
    (g0 : CanonicalMetric U hU i)
    (hterminal :
      letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (x : Piece U i) v w, g0.inner x v w = B (t0, x) v w) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ g : ℝ → CanonicalMetric U hU i,
      RiemannianMetric.IsSmoothFamilyOn g J ∧
      (∀ t ∈ J, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w) ∧
      g t0 = g0 := by
  classical
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hex : ∀ t : J, ∃ g : CanonicalMetric U hU i,
      ∀ (x : Piece U i) v w, g.inner x v w = B (t, x) v w := by
    intro t
    apply ChartDistance.exists_canonicalMetric_of_coordinate_limit U hU
      (fun k x => Bseq k (t, x)) (fun x => B (t, x)) i ?_
      (fun k x hx => hsymm k t t.property x hx)
      (fun x hx => hconv t t.property x hx)
      (fun x hx => hlower t t.property x hx)
    exact hB.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x hx => ⟨t.property, hx⟩)
  choose gs hgs using hex
  let g : ℝ → CanonicalMetric U hU i :=
    fun t => if ht : t ∈ J then gs ⟨t, ht⟩ else gs ⟨t0, ht0⟩
  have hcoeff : ∀ t ∈ J, ∀ (x : Piece U i) v w,
      (g t).inner x v w = B (t, x) v w := by
    intro t ht x v w
    simp only [g, dif_pos ht]
    exact hgs ⟨t, ht⟩ x v w
  refine ⟨g, ChartDistance.canonicalMetric_isSmoothFamilyOn_of_coefficients
    U hU i g B hB hcoeff, hcoeff, ?_⟩
  have hinner : (g t0).inner = g0.inner := by
    funext x
    ext v w
    exact (hcoeff t0 ht0 x v w).trans (hterminal x v w).symm
  generalize g t0 = gt at hinner ⊢
  cases gt
  cases g0
  cases hinner
  rfl

end PoincareConjecture.M47
