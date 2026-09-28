import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.BallData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}
  {P : ParabolicSpacetimeRescaling R Q hQ a}

noncomputable def ballNeighborhoodForward (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (K : SpacetimeInterval)
    (e : BasedBallSpacetimeNeighborhood R.spacetime R.slices R.timeIntervals t p r K) :
    BasedBallSpacetimeNeighborhood P.realization.spacetime P.realization.slices
      R.timeIntervals (parabolicTime Q a t) (P.sliceIdentification t p)
      (Real.sqrt Q * r) (parabolicInterval Q hQ a K) := by
  let f := sliceBallHomeomorph P t p r
  refine {
    radius_pos := mul_pos (Real.sqrt_pos.mpr hQ) e.radius_pos
    base_mem := (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).2 e.base_mem
    embedding := embeddingPrecomposeHomeomorph
      (D.embeddingEquiv _ K e.embedding) f.symm
    based := ?_ }
  intro x
  change (D.embeddingEquiv _ K e.embedding).toSpacetime
    (⟨parabolicTime Q a t,
      (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).2 e.base_mem⟩,
      f.symm x) = x.val.val
  rw [D.embedding_forward]
  have htime : (P.intervalTransport.diffeomorph K).symm
      ⟨parabolicTime Q a t,
        (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).2 e.base_mem⟩ =
          ⟨t, e.base_mem⟩ := by
    apply Subtype.ext
    rw [P.intervalTransport.inverse_eq]
    exact parabolicTimeInv_parabolicTime Q hQ a t
  rw [htime]
  exact (e.based (f.symm x)).trans (sliceBallHomeomorph_inverse_source P t p r x)

noncomputable def ballNeighborhoodInverse (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (hr : 0 < r) (K : SpacetimeInterval)
    (e : BasedBallSpacetimeNeighborhood P.realization.spacetime P.realization.slices
      R.timeIntervals (parabolicTime Q a t) (P.sliceIdentification t p)
      (Real.sqrt Q * r) (parabolicInterval Q hQ a K)) :
    BasedBallSpacetimeNeighborhood R.spacetime R.slices R.timeIntervals t p r K := by
  let f := sliceBallHomeomorph P t p r
  refine {
    radius_pos := hr
    base_mem := (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).1 e.base_mem
    embedding := (D.embeddingEquiv _ K).symm
      (embeddingPrecomposeHomeomorph e.embedding f)
    based := ?_ }
  intro x
  rw [D.embedding_inverse]
  change e.embedding.toSpacetime (P.intervalTransport.diffeomorph K
    ⟨t, (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).1 e.base_mem⟩, f x) = x.val.val
  have htime : P.intervalTransport.diffeomorph K
      ⟨t, (parabolicTime_mem_parabolicInterval_iff Q hQ a K t).1 e.base_mem⟩ =
      ⟨parabolicTime Q a t, e.base_mem⟩ := by
    apply Subtype.ext
    rw [P.intervalTransport.forward_eq]
    rfl
  rw [htime]
  exact (e.based (f x)).trans (sliceBallHomeomorph_source P t p r x)

theorem ballNeighborhoodForward_map (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (K : SpacetimeInterval)
    (e : BasedBallSpacetimeNeighborhood R.spacetime R.slices R.timeIntervals t p r K)
    (s : (R.timeIntervals.interval (parabolicInterval Q hQ a K)).Point)
    (x : (P.realization.slices (parabolicTime Q a t)).metricOnPoints.ball
      (P.sliceIdentification t p) (Real.sqrt Q * r)) :
    (ballNeighborhoodForward D t p r K e).embedding.toSpacetime (s, x) =
      e.embedding.toSpacetime ((P.intervalTransport.diffeomorph K).symm s,
        (sliceBallHomeomorph P t p r).symm x) :=
  D.embedding_forward _ K e.embedding s ((sliceBallHomeomorph P t p r).symm x)

theorem ballNeighborhoodInverse_map (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (hr : 0 < r) (K : SpacetimeInterval)
    (e : BasedBallSpacetimeNeighborhood P.realization.spacetime P.realization.slices
      R.timeIntervals (parabolicTime Q a t) (P.sliceIdentification t p)
      (Real.sqrt Q * r) (parabolicInterval Q hQ a K))
    (s : (R.timeIntervals.interval K).Point) (x : (R.slices t).metricOnPoints.ball p r) :
    (ballNeighborhoodInverse D t p r hr K e).embedding.toSpacetime (s, x) =
      e.embedding.toSpacetime (P.intervalTransport.diffeomorph K s,
        sliceBallHomeomorph P t p r x) :=
  D.embedding_inverse _ K
    (embeddingPrecomposeHomeomorph e.embedding (sliceBallHomeomorph P t p r)) s x

noncomputable def ballNeighborhoodEquiv (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (hr : 0 < r) (K : SpacetimeInterval) :
    BasedBallSpacetimeNeighborhood R.spacetime R.slices R.timeIntervals t p r K ≃
      BasedBallSpacetimeNeighborhood P.realization.spacetime P.realization.slices
        R.timeIntervals (parabolicTime Q a t) (P.sliceIdentification t p)
        (Real.sqrt Q * r) (parabolicInterval Q hQ a K) where
  toFun := ballNeighborhoodForward D t p r K
  invFun := ballNeighborhoodInverse D t p r hr K
  left_inv e := by
    apply basedBallNeighborhood_ext
    apply compatibleEmbedding_ext
    funext z
    rcases z with ⟨s, x⟩
    rw [ballNeighborhoodInverse_map, ballNeighborhoodForward_map,
      Diffeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  right_inv e := by
    apply basedBallNeighborhood_ext
    apply compatibleEmbedding_ext
    funext z
    rcases z with ⟨s, x⟩
    rw [ballNeighborhoodForward_map, ballNeighborhoodInverse_map,
      Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem ballNeighborhoodTransport (D : ParabolicDomainTransport.{u, u} P)
    (t : ℝ) (p : (R.slices t).Point) (r : ℝ) (hr : 0 < r) (K : SpacetimeInterval) :
    Nonempty (ParabolicBallNeighborhoodTransport P t p r K) := by
  refine ⟨{
    ballHomeomorph := sliceBallHomeomorph P t p r
    ball_forward := sliceBallHomeomorph_val P t p r
    ball_inverse := sliceBallHomeomorph_inverse_val P t p r
    source_inclusion := sliceBallHomeomorph_source P t p r
    neighborhoodEquiv := ballNeighborhoodEquiv D t p r hr K
    neighborhood_forward := ?_
    neighborhood_inverse := ?_
    image_eq := ?_
    closed_time_iff := closed_time_iff Q hQ a K
    backward_parabolic_time_iff := backward_parabolic_time_iff Q hQ a K t r }⟩
  · intro e s x
    change (ballNeighborhoodForward D t p r K e).embedding.toSpacetime
      (s, sliceBallHomeomorph P t p r x) = _
    rw [ballNeighborhoodForward_map, Homeomorph.symm_apply_apply]
  · intro e s x
    change (ballNeighborhoodInverse D t p r hr K e).embedding.toSpacetime
      (s, (sliceBallHomeomorph P t p r).symm x) = _
    rw [ballNeighborhoodInverse_map, Homeomorph.apply_symm_apply]
  · intro e
    ext q
    constructor
    · rintro ⟨⟨s, x⟩, rfl⟩
      exact ⟨((P.intervalTransport.diffeomorph K).symm s,
        (sliceBallHomeomorph P t p r).symm x),
        (ballNeighborhoodForward_map D t p r K e s x).symm⟩
    · rintro ⟨⟨s, x⟩, rfl⟩
      refine ⟨(P.intervalTransport.diffeomorph K s, sliceBallHomeomorph P t p r x), ?_⟩
      change (ballNeighborhoodForward D t p r K e).embedding.toSpacetime _ = _
      rw [ballNeighborhoodForward_map, Diffeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

end PoincareConjecture.ParabolicRescaling
