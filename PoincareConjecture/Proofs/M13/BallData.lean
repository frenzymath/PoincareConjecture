import PoincareConjecture.Proofs.M13.DomainLaws
import PoincareConjecture.Proofs.M13.Length








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M13

noncomputable def embeddingPrecomposeHomeomorph
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I} {T : SmoothSpacetimeInterval K}
    {C : Type v} {C' : Type w} [TopologicalSpace C] [TopologicalSpace C']
    (e : CompatibleSpacetimeEmbedding S T C) (f : C' ≃ₜ C) :
    CompatibleSpacetimeEmbedding S T C' where
  interval_subset := e.interval_subset
  toSpacetime p := e.toSpacetime (p.1, f p.2)
  embedding := e.embedding.comp ((Homeomorph.refl T.Point).prodCongr f).isEmbedding
  time_eq p := e.time_eq (p.1, f p.2)
  worldline_smooth x := e.worldline_smooth (f x)
  worldline_derivative t x := e.worldline_derivative t (f x)

theorem basedBallNeighborhood_ext
    {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    {S : GeneralizedFlowSpacetime n X time I}
    {D : ∀ t, SpacetimeSliceGeometry S t} {T : SpacetimeIntervalSystem}
    {t : ℝ} {p : (D t).Point} {r : ℝ} {K : SpacetimeInterval}
    {e f : BasedBallSpacetimeNeighborhood S D T t p r K}
    (h : e.embedding = f.embedding) : e = f := by
  cases e
  cases f
  cases h
  rfl

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

noncomputable def sliceBallHomeomorph (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) :
    ((R.slices t).metricOnPoints.ball p r) ≃ₜ
      ((P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
        (P.sliceIdentification t p) (Real.sqrt Q * r)) := by
  apply (P.sliceIdentification t).toHomeomorph.subtype
  intro x
  have himage := homothety_ball_image (R.slices t).metricOnPoints
    (P.realization.slices (parabolicTime Q a t)).metricOnPoints
    (P.sliceIdentification t) Q hQ (P.slice_metric t) p r
  change x ∈ (R.slices t).metricOnPoints.ball p r ↔
    P.sliceIdentification t x ∈ _
  rw [← himage]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact (P.sliceIdentification t).injective hyx ▸ hy

theorem sliceBallHomeomorph_val (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ)
    (x : (R.slices t).metricOnPoints.ball p r) :
    (sliceBallHomeomorph P t p r x).val = P.sliceIdentification t x.val := rfl

theorem sliceBallHomeomorph_inverse_val (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ)
    (x : (P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
      (P.sliceIdentification t p) (Real.sqrt Q * r)) :
    ((sliceBallHomeomorph P t p r).symm x).val =
      (P.sliceIdentification t).symm x.val := rfl

theorem sliceBallHomeomorph_source (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ)
    (x : (R.slices t).metricOnPoints.ball p r) :
    (sliceBallHomeomorph P t p r x).val.val = x.val.val :=
  P.sliceIdentification_eq t x.val

theorem sliceBallHomeomorph_inverse_source (P : ParabolicSpacetimeRescaling R Q hQ a)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ)
    (x : (P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
      (P.sliceIdentification t p) (Real.sqrt Q * r)) :
    ((sliceBallHomeomorph P t p r).symm x).val.val = x.val.val := by
  have h := sliceBallHomeomorph_source P t p r ((sliceBallHomeomorph P t p r).symm x)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

end PoincareConjecture.M13
