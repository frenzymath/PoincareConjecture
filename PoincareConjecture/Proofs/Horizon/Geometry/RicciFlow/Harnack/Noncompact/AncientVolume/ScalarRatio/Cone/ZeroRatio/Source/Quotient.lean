import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.DistanceMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
  {D : ∀ i j, C(X i × X j, ℝ)}
  (O : OverlapSystem X)
  (hrel : ∀ i j (x : X i) (y : X j), O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0)
  {B : Type*} [MetricSpace B] (f : ∀ i, X i → B)
  (hf : ∀ i j x y, dist (f i x) (f j y) = D i j (x, y))

def quotientRealization : Quotient O.setoid → B :=
  Quotient.lift (fun a : Σ i, X i => f a.1 a.2) (by
    intro a b hab
    apply dist_eq_zero.mp
    exact (hf a.1 b.1 a.2 b.2).trans ((hrel a.1 b.1 a.2 b.2).mp hab))

@[simp] theorem quotientRealization_include (i : ι) (x : X i) :
    quotientRealization O hrel f hf (O.include i x) = f i x := rfl

theorem quotientRealization_injective :
    Function.Injective (quotientRealization O hrel f hf) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h a =>
    induction r using Quotient.inductionOn with
    | h b =>
      intro hab
      apply Quotient.sound
      apply (hrel a.1 b.1 a.2 b.2).mpr
      exact (hf a.1 b.1 a.2 b.2).symm.trans (dist_eq_zero.mpr hab)

theorem range_quotientRealization :
    range (quotientRealization O hrel f hf) = ⋃ i, range (f i) := by
  ext b
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h a => exact mem_iUnion.mpr ⟨a.1, ⟨a.2, rfl⟩⟩
  · intro hb
    obtain ⟨i, x, rfl⟩ := mem_iUnion.mp hb
    exact ⟨O.include i x, rfl⟩

theorem continuous_quotientRealization (hcontinuous : ∀ i, Continuous (f i)) :
    Continuous (quotientRealization O hrel f hf) :=
  (continuous_sigma fun i => hcontinuous i).quotient_lift _

theorem quotientRealization_image (S : Set (Quotient O.setoid)) :
    quotientRealization O hrel f hf '' S = ⋃ i, f i '' (O.include i ⁻¹' S) := by
  ext b
  constructor
  · rintro ⟨q, hq, rfl⟩
    induction q using Quotient.inductionOn with
    | h a => exact mem_iUnion.mpr ⟨a.1, ⟨a.2, hq, rfl⟩⟩
  · intro hb
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hb
    exact ⟨O.include i x, hx, rfl⟩

theorem isOpenMap_quotientRealization (hopen : ∀ i, IsOpenMap (f i)) :
    IsOpenMap (quotientRealization O hrel f hf) := by
  intro S hS
  rw [quotientRealization_image]
  exact isOpen_iUnion fun i => hopen i _
    (hS.preimage (O.include_isOpenEmbedding i).continuous)

theorem isOpenEmbedding_quotientRealization
    (hopen : ∀ i, Topology.IsOpenEmbedding (f i)) :
    Topology.IsOpenEmbedding (quotientRealization O hrel f hf) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_quotientRealization O hrel f hf fun i => (hopen i).continuous)
    (quotientRealization_injective O hrel f hf)
    (isOpenMap_quotientRealization O hrel f hf fun i => (hopen i).isOpenMap)

variable {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
  {e : ∀ k i, X i → M k}
  (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
    (𝓝 (D i j (x, y))))

theorem dist_quotientRealization (q r : Quotient O.setoid) :
    dist (quotientRealization O hrel f hf q) (quotientRealization O hrel f hf r) =
      quotientDistance hD O hrel q r := by
  induction q using Quotient.inductionOn with
  | h a =>
    induction r using Quotient.inductionOn with
    | h b => exact hf a.1 b.1 a.2 b.2

theorem isometry_quotientRealization
    [∀ i, LocallyCompactSpace (X i)]
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r)) :
    letI := quotientMetricSpace hD O hrel L he c hc hlower hopen hconn
    Isometry (quotientRealization O hrel f hf) := by
  let := quotientMetricSpace hD O hrel L he c hc hlower hopen hconn
  apply Isometry.of_dist_eq
  intro q r
  exact dist_quotientRealization O hrel f hf hD q r

end PoincareConjecture.ChartDistance
