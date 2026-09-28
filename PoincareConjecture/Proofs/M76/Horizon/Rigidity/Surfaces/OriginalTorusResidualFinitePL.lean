import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualGeometricSides
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

omit [DecidableEq E] in
private theorem finitePL_affine_interval {l u : ℝ} (hlu : l < u)
    (A : ℝ →ᴬ[ℝ] E) : FinitePiecewiseAffineOn A (Icc l u) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc hlu
  exact ⟨K, hK, hKs, K.affineOnFaces_affine A⟩

theorem residualEdgePath_affine_formula
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) (t : Icc (0 : ℝ) 1) :
    (residualEdgePath K e b t : E) =
      (if b then
        ContinuousAffineMap.lineMap
          ((residualEdgeEndpoints K e).2 : E)
          ((residualEdgeEndpoints K e).1 : E)
      else
        ContinuousAffineMap.lineMap
          ((residualEdgeEndpoints K e).1 : E)
          ((residualEdgeEndpoints K e).2 : E)) (t : ℝ) := by
  let u := (residualEdgeEndpoints K e).1
  let v := (residualEdgeEndpoints K e).2
  have huv : K.vertexAbstractComplex.edgeGraph.Adj u v := by
    refine ⟨(residualEdgeEndpoints_spec K e).1, ?_⟩
    rw [← residualEdgeEndpoints_spec K e |>.2]
    exact e.property.1
  cases b with
  | false =>
      change (K.geometricEdgePath huv t : E) = _
      change (Path.segmentIn K.space _ _ _ t : E) = _
      rw [Path.segmentIn_apply]
      rfl
  | true =>
      simp only [residualEdgePath, if_true]
      rw [← K.geometricEdgePath_symm huv]
      change (K.geometricEdgePath huv.symm t : E) = _
      change (Path.segmentIn K.space _ _ _ t : E) = _
      rw [Path.segmentIn_apply]
      rfl

theorem residualEdgePath_finite_piecewise_affine
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) :
    ∃ f : ℝ → E,
      FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1,
          f (t : ℝ) = (residualEdgePath K e b t : E) := by
  let A : ℝ →ᴬ[ℝ] E :=
    if b then
      ContinuousAffineMap.lineMap
        ((residualEdgeEndpoints K e).2 : E)
        ((residualEdgeEndpoints K e).1 : E)
    else
      ContinuousAffineMap.lineMap
        ((residualEdgeEndpoints K e).1 : E)
        ((residualEdgeEndpoints K e).2 : E)
  refine ⟨A, finitePL_affine_interval (by norm_num) A, ?_⟩
  intro t
  exact (residualEdgePath_affine_formula K e b t).symm

theorem residualEdgePath_image
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) :
    Set.range (fun t : Icc (0 : ℝ) 1 =>
      (residualEdgePath K e b t : E)) =
      segment ℝ
        (if b then ((residualEdgeEndpoints K e).2 : E) else
          ((residualEdgeEndpoints K e).1 : E))
        (if b then ((residualEdgeEndpoints K e).1 : E) else
          ((residualEdgeEndpoints K e).2 : E)) := by
  let u : E := (residualEdgeEndpoints K e).1
  let v : E := (residualEdgeEndpoints K e).2
  have huv : u ≠ v := by
    intro h
    apply (residualEdgeEndpoints_spec K e).1
    exact Subtype.ext h
  let A : ℝ →ᴬ[ℝ] E := if b then
    ContinuousAffineMap.lineMap (R := ℝ) v u else
    ContinuousAffineMap.lineMap (R := ℝ) u v
  have hA (t : Icc (0 : ℝ) 1) :
      (residualEdgePath K e b t : E) = A (t : ℝ) := by
    simpa only [A, u, v, ContinuousAffineMap.coe_toAffineMap,
      ContinuousAffineMap.coe_lineMap_eq] using
      residualEdgePath_affine_formula K e b t
  have hrange : Set.range (fun t : Icc (0 : ℝ) 1 =>
      (residualEdgePath K e b t : E)) = A '' Icc (0 : ℝ) 1 := by
    calc
      _ = Set.range (fun t : Icc (0 : ℝ) 1 => A (t : ℝ)) := by
        congr 1
        funext t
        exact hA t
      _ = A '' Set.range (Subtype.val : Icc (0 : ℝ) 1 → ℝ) :=
        Set.range_comp A Subtype.val
      _ = A '' Icc (0 : ℝ) 1 := by rw [Subtype.range_val]
  calc
    _ = A '' Icc (0 : ℝ) 1 := hrange
    _ = segment ℝ
        (if b then ((residualEdgeEndpoints K e).2 : E) else
          ((residualEdgeEndpoints K e).1 : E))
        (if b then ((residualEdgeEndpoints K e).1 : E) else
          ((residualEdgeEndpoints K e).2 : E)) := by
      cases b
      · have h := (segment_eq_image_lineMap ℝ u v).symm
        simpa [A, u, v, ContinuousAffineMap.coe_lineMap_eq,
          AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h
      · have h := (segment_eq_image_lineMap ℝ v u).symm
        simpa [A, u, v, ContinuousAffineMap.coe_lineMap_eq,
          AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h

theorem residualEdgePath_isFinitePLBallPair
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) [FiniteDimensional ℝ E] :
    IsFinitePLBallPair ℝ
      (Set.range (fun t : Icc (0 : ℝ) 1 =>
        (residualEdgePath K e b t : E)))
      ({if b then ((residualEdgeEndpoints K e).2 : E) else
          ((residualEdgeEndpoints K e).1 : E),
        if b then ((residualEdgeEndpoints K e).1 : E) else
          ((residualEdgeEndpoints K e).2 : E)} : Set E) := by
  rw [residualEdgePath_image]
  let u : E := (residualEdgeEndpoints K e).1
  let v : E := (residualEdgeEndpoints K e).2
  have huv : u ≠ v := by
    intro h
    apply (residualEdgeEndpoints_spec K e).1
    exact Subtype.ext h
  cases b
  · have h := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 by norm_num)
      (ContinuousAffineMap.lineMap (R := ℝ) u v)
      (AffineMap.lineMap_injective ℝ huv).injOn
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [segment_eq_image_lineMap ℝ u v]
    simpa [ContinuousAffineMap.coe_lineMap_eq,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h
  · have h := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 by norm_num)
      (ContinuousAffineMap.lineMap (R := ℝ) v u)
      (AffineMap.lineMap_injective ℝ huv.symm).injOn
    simp only [↓reduceIte]
    rw [segment_eq_image_lineMap ℝ v u]
    simpa [ContinuousAffineMap.coe_lineMap_eq,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h

theorem residualBoundarySourcePath_finite_piecewise_affine
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (b : Bool) :
    ∃ f : ℝ → E,
      FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1,
          f (t : ℝ) = (residualBoundarySourcePath K hL i b t : E) := by
  exact residualEdgePath_finite_piecewise_affine K
    ((Finset.equivFinOfCardEq hL).symm i).val b

theorem residualBoundarySourcePath_isFinitePLBallPair
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (b : Bool) [FiniteDimensional ℝ E] :
    IsFinitePLBallPair ℝ
      (Set.range (fun t : Icc (0 : ℝ) 1 =>
        (residualBoundarySourcePath K hL i b t : E)))
      ({if b then
          ((residualEdgeEndpoints K ((Finset.equivFinOfCardEq hL).symm i).val).2 : E)
        else
          ((residualEdgeEndpoints K ((Finset.equivFinOfCardEq hL).symm i).val).1 : E),
        if b then
          ((residualEdgeEndpoints K ((Finset.equivFinOfCardEq hL).symm i).val).1 : E)
        else
          ((residualEdgeEndpoints K ((Finset.equivFinOfCardEq hL).symm i).val).2 : E)} : Set E) := by
  simpa only [residualBoundarySourcePath] using
    residualEdgePath_isFinitePLBallPair K
      ((Finset.equivFinOfCardEq hL).symm i).val b

private def reverseParameter (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - (t : ℝ), by have ht := t.2.2; linarith, by have ht := t.2.1; linarith⟩


noncomputable def residualEdgeOrientedPath
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (b : Bool) (t : Icc (0 : ℝ) 1) : E :=
  if b then residualEdgePath K e true (reverseParameter t) else
    residualEdgePath K e false t

theorem residualEdgeOrientedPath_eq
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (t : Icc (0 : ℝ) 1) :
    residualEdgeOrientedPath K e false t =
      residualEdgeOrientedPath K e true t := by
  have hrev : unitInterval.symm (reverseParameter t) = t := by
    apply Subtype.ext
    simp [reverseParameter, unitInterval.symm]
  simp only [residualEdgeOrientedPath, Bool.false_eq_true, ↓reduceIte]
  rw [residualEdgePath_affine_formula K e false t,
    residualEdgePath_affine_formula K e true (reverseParameter t)]
  change AffineMap.lineMap
      ((residualEdgeEndpoints K e).1 : E)
      ((residualEdgeEndpoints K e).2 : E) (t : ℝ) =
    AffineMap.lineMap
      ((residualEdgeEndpoints K e).2 : E)
      ((residualEdgeEndpoints K e).1 : E) (1 - (t : ℝ))
  simp [AffineMap.lineMap_apply_module]
  ac_rfl

theorem residualEdgeOrientedPath_affine_formula
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    (t : Icc (0 : ℝ) 1) :
    residualEdgeOrientedPath K e false t =
      ContinuousAffineMap.lineMap
        ((residualEdgeEndpoints K e).1 : E)
        ((residualEdgeEndpoints K e).2 : E) (t : ℝ) := by
  exact residualEdgePath_affine_formula K e false t

theorem residualEdgeOrientedPath_finite_piecewise_affine
    (K : SimplicialComplex ℝ E)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    ∃ f : ℝ → E,
      FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1,
          f (t : ℝ) = residualEdgeOrientedPath K e false t := by
  refine ⟨ContinuousAffineMap.lineMap
      ((residualEdgeEndpoints K e).1 : E)
      ((residualEdgeEndpoints K e).2 : E),
    finitePL_affine_interval (by norm_num) _, ?_⟩
  intro t
  exact (residualEdgeOrientedPath_affine_formula K e t).symm

theorem residualBoundaryOrientedPath_eq
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (t : Icc (0 : ℝ) 1) :
    residualEdgeOrientedPath K
        ((Finset.equivFinOfCardEq hL).symm i).val false t =
      residualEdgeOrientedPath K
        ((Finset.equivFinOfCardEq hL).symm i).val true t := by
  exact residualEdgeOrientedPath_eq K _ t

noncomputable def residualBoundaryOrientedPath
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (b : Bool)
    (t : Icc (0 : ℝ) 1) : E :=
  residualEdgeOrientedPath K ((Finset.equivFinOfCardEq hL).symm i).val b t

theorem residualBoundaryOrientedPath_sidePair
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) (t : Icc (0 : ℝ) 1) :
    residualBoundaryOrientedPath K hL i false t =
      residualBoundaryOrientedPath K hL i true t := by
  exact residualBoundaryOrientedPath_eq K hL i t

theorem residualBoundaryOrientedPath_continuous
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) :
    Continuous (residualBoundaryOrientedPath K hL i false) := by
  let e := ((Finset.equivFinOfCardEq hL).symm i).val
  have hline : Continuous (fun t : Icc (0 : ℝ) 1 =>
      ContinuousAffineMap.lineMap
        ((residualEdgeEndpoints K e).1 : E)
        ((residualEdgeEndpoints K e).2 : E) (t : ℝ)) := by
    fun_prop
  apply hline.congr
  intro t
  exact (residualEdgeOrientedPath_affine_formula K e t).symm

theorem residualBoundaryOrientedPath_finite_piecewise_affine
    (K : SimplicialComplex ℝ E)
    {L : Finset (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
    (hL : L.card = 2) (i : Fin 2) :
    ∃ f : ℝ → E,
      FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) ∧
        ∀ t : Icc (0 : ℝ) 1,
          f (t : ℝ) = residualBoundaryOrientedPath K hL i false t := by
  let e := ((Finset.equivFinOfCardEq hL).symm i).val
  obtain ⟨f, hf, hfe⟩ := residualEdgeOrientedPath_finite_piecewise_affine K e
  refine ⟨f, hf, ?_⟩
  intro t
  exact hfe t

end PoincareConjecture.M76
