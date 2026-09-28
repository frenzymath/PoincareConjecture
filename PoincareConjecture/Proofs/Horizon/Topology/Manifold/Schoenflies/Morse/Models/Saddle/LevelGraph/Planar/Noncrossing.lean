import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Clearance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Arcs.Noncrossing



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem planarProjection_injOn_level
    {f : S2 -> E3} (hf : Function.Injective f)
    {v : E3} (hv : ‖v‖ = 1) (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y) (c : Real) :
    InjOn (fun q => planarProjection J (D (f q))) {q | inner Real v (f q) = c} := by
  intro q hq z hz heq
  apply hf
  apply D.injective
  apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
  apply Prod.ext
  · change inner Real v (D (f q)) = inner Real v (D (f z))
    rw [hDheight, hDheight, hq, hz]
  · exact J.symm.injective heq




theorem exists_exterior_noncrossing_square
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (hep : e 0 = p)
    {a : Real} (ha : 0 < a) (has : closedBall (0 : E2) a ⊆ e.source)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v)
    {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ ball (0 : E2) a ∧
      (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
        (planarProjection J (D (f q)) ∈ closedSquare r ↔ q ∈ e '' closedSquare r)) ∧
      (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
        (planarProjection J (D (f q)) ∈ openSquare r ↔ q ∈ e '' openSquare r)) ∧
      {q : S2 | inner Real v (f q) = inner Real v (f p) ∧
        planarProjection J (D (f q)) ∈ closedSquare r \ openSquare r} =
          range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      Function.Injective (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      ∀ (α β : Real -> S2),
        ContinuousOn α (Icc (0 : Real) 1) -> ContinuousOn β (Icc (0 : Real) 1) ->
        MapsTo α (Icc (0 : Real) 1)
          ({q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r) ->
        MapsTo β (Icc (0 : Real) 1)
          ({q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r) ->
        α 0 = e (contact r (1, 1)) -> α 1 = e (contact r (0, 0)) ->
        β 0 = e (contact r (0, 1)) -> β 1 = e (contact r (1, 0)) ->
        ¬ Disjoint (α '' Icc (0 : Real) 1) (β '' Icc (0 : Real) 1) := by
  obtain ⟨r, hr, hrε, hrs, hclosed, hopen, hcontacts, hinj⟩ :=
    exists_planar_clearance hf hv p e hep ha has J D hDheight hgraph hε
  refine ⟨r, hr, hrε, hrs, hclosed, hopen, hcontacts, hinj, ?_⟩
  intro α β hα hβ hαK hβK hα0 hα1 hβ0 hβ1 hdisj
  let π : S2 -> E2 := fun q => planarProjection J (D (f q))
  have hπ : Continuous π :=
    J.symm.continuous.comp ((Real ∙ v)ᗮ.orthogonalProjectionOnto.continuous.comp
      (D.contMDiff.continuous.comp hf.contMDiff.continuous))
  have hπi := planarProjection_injOn_level hf.isEmbedding.injective hv J D hDheight
    (inner Real v (f p))
  have hout (q : S2)
      (hq : q ∈ {q | inner Real v (f q) = inner Real v (f p)} \ e '' openSquare r) :
      r ≤ PlaneArcs.squareGauge (π q) := by
    apply le_of_not_gt
    intro hlt
    apply hq.2
    apply (hopen q hq.1).mp
    exact ⟨(le_max_left _ _).trans_lt hlt, (le_max_right _ _).trans_lt hlt⟩
  have hend (i : Fin 2 × Fin 2) : π (e (contact r i)) = PlaneArcs.squareCorner r i := by
    change planarProjection J (D (f (e (contact r i)))) = _
    rw [hgraph _ (ball_subset_closedBall (hrs (contact_mem hr i).1.1)),
      planarProjection_graph]
    rfl
  apply PlaneArcs.not_disjoint_exterior_opposite_corners hr (π ∘ α) (π ∘ β)
    (hπ.comp_continuousOn hα) (hπ.comp_continuousOn hβ)
    (fun t ht => hout _ (hαK ht)) (fun t ht => hout _ (hβK ht))
    (by simp only [comp_apply, hα0, hend]) (by simp only [comp_apply, hα1, hend])
    (by simp only [comp_apply, hβ0, hend]) (by simp only [comp_apply, hβ1, hend])
  apply disjoint_left.mpr
  rintro x ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
  have heq' : β t = α s := hπi (hβK ht).1 (hαK hs).1 heq
  exact disjoint_left.mp hdisj ⟨s, hs, rfl⟩ ⟨t, ht, heq'⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
