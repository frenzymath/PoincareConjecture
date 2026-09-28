import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTriangleCopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

abbrev ambientEdge
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) : Finset E :=
  e.val.map (Function.Embedding.subtype _)

theorem ambientEdge_eq_pair
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    (ambientEdge K e : Set E) =
      {((PoincareConjecture.M76.residualEdgeEndpoints K e).1 : E),
       ((PoincareConjecture.M76.residualEdgeEndpoints K e).2 : E)} := by
  have h := congrArg (fun q : Finset K.vertices =>
      q.map (Function.Embedding.subtype _))
    (PoincareConjecture.M76.residualEdgeEndpoints_spec K e).2
  have hfin : ambientEdge K e =
      ({((PoincareConjecture.M76.residualEdgeEndpoints K e).1 : E),
        ((PoincareConjecture.M76.residualEdgeEndpoints K e).2 : E)} : Finset E) := by
    change e.val.map (Function.Embedding.subtype _) = _
    simpa only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using h
  simpa only [Finset.coe_insert, Finset.coe_singleton,
    Function.Embedding.coe_subtype] using
    congrArg (fun q : Finset E => (q : Set E)) hfin

noncomputable def copiedEdgePath
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) (t : Icc (0 : ℝ) 1) : E × ℝ :=
  inclusion (E := E) (label s)
    (ContinuousAffineMap.lineMap
      ((PoincareConjecture.M76.residualEdgeEndpoints K e).1 : E)
      ((PoincareConjecture.M76.residualEdgeEndpoints K e).2 : E) (t : ℝ))

theorem copiedEdgePath_image
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    Set.range (copiedEdgePath K label s e he) =
      inclusion (E := E) (label s) '' convexHull ℝ (ambientEdge K e : Set E) := by
  let u : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).1
  let v : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).2
  have huv : u ≠ v := by
    intro h
    apply PoincareConjecture.M76.residualEdgeEndpoints_spec K e |>.1
    exact Subtype.ext h
  have hseg : convexHull ℝ (ambientEdge K e : Set E) = segment ℝ u v := by
    rw [ambientEdge_eq_pair K e, convexHull_pair]
  have hline : Set.range (fun t : Icc (0 : ℝ) 1 =>
      ContinuousAffineMap.lineMap u v (t : ℝ)) = segment ℝ u v := by
    rw [show Set.range (fun t : Icc (0 : ℝ) 1 =>
        ContinuousAffineMap.lineMap u v (t : ℝ)) =
        (ContinuousAffineMap.lineMap u v) '' Icc (0 : ℝ) 1 by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, t.property, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩]
    simpa only [ContinuousAffineMap.coe_lineMap_eq] using
      (segment_eq_image_lineMap ℝ u v).symm
  apply Subset.antisymm
  · rintro x ⟨t, rfl⟩
    refine ⟨ContinuousAffineMap.lineMap u v (t : ℝ), ?_, ?_⟩
    · rw [hseg]
      exact hline.subset (mem_range_self t)
    · rfl
  · rintro x ⟨y, hy, hxy⟩
    have hy' : y ∈ segment ℝ u v := hseg.symm ▸ hy
    have hy'' : y ∈ Set.range (fun t : Icc (0 : ℝ) 1 =>
        ContinuousAffineMap.lineMap u v (t : ℝ)) := hline.symm ▸ hy'
    rcases hy'' with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    dsimp [copiedEdgePath]
    rw [← hxy, ← ht]

theorem copiedEdgePath_projection_image
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    Prod.fst '' Set.range (copiedEdgePath K label s e he) =
      convexHull ℝ (ambientEdge K e : Set E) := by
  let u : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).1
  let v : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).2
  have hline : Set.range (fun t : Icc (0 : ℝ) 1 =>
      ContinuousAffineMap.lineMap u v (t : ℝ)) = segment ℝ u v := by
    rw [show Set.range (fun t : Icc (0 : ℝ) 1 =>
        ContinuousAffineMap.lineMap u v (t : ℝ)) =
        (ContinuousAffineMap.lineMap u v) '' Icc (0 : ℝ) 1 by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, t.property, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩]
    simpa only [ContinuousAffineMap.coe_lineMap_eq] using
      (segment_eq_image_lineMap ℝ u v).symm
  have hline_subset (t : Icc (0 : ℝ) 1) :
      ContinuousAffineMap.lineMap u v (t : ℝ) ∈
        convexHull ℝ (ambientEdge K e : Set E) := by
    rw [ambientEdge_eq_pair K e, convexHull_pair]
    exact hline.subset (mem_range_self t)
  rw [copiedEdgePath_image K label s e he]
  apply Subset.antisymm
  · rintro x ⟨z, ⟨y, hy, hzy⟩, hzx⟩
    have hxy : x = y := by
      rw [← hzx, ← hzy]
      rfl
    exact hxy ▸ hy
  · rintro x hx
    refine ⟨(x, label s), ⟨x, hx, rfl⟩, rfl⟩

theorem copiedEdgePath_isFinitePLBallPair
    (label : Triangle K → ℝ) (s : Triangle K)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (he : ambientEdge K e ⊆ s.val) :
    IsFinitePLBallPair ℝ
      (Set.range (copiedEdgePath K label s e he))
      ({inclusion (E := E) (label s) (PoincareConjecture.M76.residualEdgeEndpoints K e).1,
        inclusion (E := E) (label s) (PoincareConjecture.M76.residualEdgeEndpoints K e).2} : Set (E × ℝ)) := by
  let u : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).1
  let v : E := (PoincareConjecture.M76.residualEdgeEndpoints K e).2
  have huv : u ≠ v := by
    intro h
    apply PoincareConjecture.M76.residualEdgeEndpoints_spec K e |>.1
    exact Subtype.ext h
  let A : ℝ →ᴬ[ℝ] (E × ℝ) :=
    (ContinuousAffineMap.lineMap u v).prod (ContinuousAffineMap.const ℝ ℝ (label s))
  have hAinj : InjOn A (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply AffineMap.lineMap_injective ℝ huv
    exact congrArg Prod.fst hxy
  have h := isFinitePLBallPair_affine_interval
    (show (0 : ℝ) < 1 by norm_num) A hAinj
  rw [copiedEdgePath_image K label s e he]
  have hAimage : A '' Icc (0 : ℝ) 1 =
      inclusion (E := E) (label s) '' convexHull ℝ (ambientEdge K e : Set E) := by
    apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      refine ⟨ContinuousAffineMap.lineMap u v t, ?_, rfl⟩
      rw [ambientEdge_eq_pair K e, convexHull_pair]
      exact (show ContinuousAffineMap.lineMap u v t ∈ segment ℝ u v from
        (segment_eq_image_lineMap ℝ u v).symm ▸ ⟨t, ht, rfl⟩)
    · rintro z ⟨y, hy, rfl⟩
      rw [ambientEdge_eq_pair K e, convexHull_pair] at hy
      have hy' : y ∈ segment ℝ u v := by simpa [u, v] using hy
      rw [segment_eq_image_lineMap ℝ u v] at hy'
      obtain ⟨t, ht, hty⟩ := hy'
      refine ⟨t, ht, ?_⟩
      rw [← hty]
      rfl
  have hend :
      ({inclusion (E := E) (label s) (PoincareConjecture.M76.residualEdgeEndpoints K e).1,
        inclusion (E := E) (label s) (PoincareConjecture.M76.residualEdgeEndpoints K e).2} : Set (E × ℝ)) =
      ({A 0, A 1} : Set (E × ℝ)) := by
    ext z
    simp [A, inclusion, u, v, ContinuousAffineMap.coe_prod,
      ContinuousAffineMap.coe_lineMap_eq, ContinuousAffineMap.coe_const,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
  rw [← hAimage, hend]
  exact h

end PoincareConjecture.M76.OriginalTriangleCopies
