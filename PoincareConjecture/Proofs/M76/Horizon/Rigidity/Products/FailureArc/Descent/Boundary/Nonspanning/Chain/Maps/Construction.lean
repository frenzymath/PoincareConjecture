import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Agreement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.PuncturedCopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Pasting

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainHole

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Piece" => NonspanningRetainedPiece
local notation "Index" => (Piece ⊕ Bool)

open PolygonalCrossingResolution

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  (H : NonspanningChainHole s D)

noncomputable def pieceMap {X : Type*} (f : P2 → X) (τ : C3 → X) : Index → P2 → X
  | .inl _ => f
  | .inr b => τ ∘ alternate (1 / 4) b

theorem pieceMap_agree {X : Type*} (f : P2 → X) (τ : C3 → X)
    (hdisj : Disjoint (range pL) (range pR))
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (i j : Index) (x : H.sourceSet i) (y : H.sourceSet j)
    (hxy : H.pieceCopy i x = H.pieceCopy j y) :
    pieceMap f τ i x = pieceMap f τ j y := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j
      · subst j
        change f x = f y
        exact congrArg f (congrArg (fun z : s.retainedSet i => (z : P2))
          ((s.retainedCopy_embedding i).injective hxy))
      · exact (s.retainedCopy_ne hij _ _ hxy).elim
    | inr b => exact s.retained_strip_values f τ hA hL hR hC i b _ _ hxy
  | inr b =>
    cases j with
    | inl i => exact (s.retained_strip_values f τ hA hL hR hC i b _ _ hxy.symm).symm
    | inr d => exact s.strip_values τ hdisj b d x y hxy

theorem pieceMap_PL
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {f : P2 → X} {τ : C3 → X}
    (hf : ∀ i, PolyhedralPLInCharts e f (s.retainedSet i \ interior D))
    (hτ : PolyhedralPLInCharts e τ tube) (i : Index) :
    PolyhedralPLInCharts e (pieceMap f τ i) (H.sourceSet i) := by
  cases i with
  | inl i => exact hf i
  | inr b =>
    have hmap := (finitePiecewiseAffineOn_maps (1 / 4) b).2
    have hcopy := hmap
    obtain ⟨K, hK, hKs, _⟩ := hcopy
    have hr : FinitePiecewiseAffineOn (alternate (1 / 4) b) K.space := hKs.symm ▸ hmap
    have hm : MapsTo (alternate (1 / 4) b) K.space tube :=
      hKs.symm ▸ (mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2
    simpa only [hKs, pieceMap, sourceSet] using hτ.comp_finitePiecewiseAffineOn K hK hr hm

theorem exists_punctured_chain_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hS : ∀ i, IsFinitePLBallPair P2 (s.retainedSet i) (frontier (s.retainedSet i)))
    (hD : IsFinitePLBallPair P2 D (frontier D))
    {f : P2 → X} {τ : C3 → X}
    (hf : ∀ i, PolyhedralPLInCharts e f (s.retainedSet i \ interior D))
    (hτ : PolyhedralPLInCharts e τ tube)
    (hdisj : Disjoint (range pL) (range pR))
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t)) :
    ∃ g : P2 → X,
      PolyhedralPLInCharts e g (T \ interior H.carrier) ∧
      (∀ i (x : H.sourceSet i), g (H.pieceCopy i x) = pieceMap f τ i x) ∧
      g '' (T \ interior H.carrier) = ⋃ i, pieceMap f τ i '' H.sourceSet i := by
  choose K hK hKs using H.source_complex hS hD
  choose c hc hcv using H.pieceCopy_representative hS hD
  have hcK (i : Index) : FinitePiecewiseAffineOn (c i) (K i).space := hKs i ▸ hc i
  have hci (i : Index) : InjOn (c i) (K i).space := by
    intro x hx y hy hxy
    apply congrArg Subtype.val ((H.pieceCopy_embedding i).injective (Subtype.ext
      ((hcv i ⟨x, (hKs i).subset hx⟩).trans
        (hxy.trans (hcv i ⟨y, (hKs i).subset hy⟩).symm))))
  have hfK (i : Index) : PolyhedralPLInCharts e (pieceMap f τ i) (K i).space :=
    hKs i ▸ H.pieceMap_PL e hf hτ i
  have hagree (i j : Index) (x : P2) (hx : x ∈ (K i).space)
      (y : P2) (hy : y ∈ (K j).space) (hxy : c i x = c j y) :
      pieceMap f τ i x = pieceMap f τ j y :=
    H.pieceMap_agree f τ hdisj hA hL hR hC i j
      ⟨x, (hKs i).subset hx⟩ ⟨y, (hKs j).subset hy⟩
      (Subtype.ext ((hcv i ⟨x, (hKs i).subset hx⟩).trans
        (hxy.trans (hcv j ⟨y, (hKs j).subset hy⟩).symm)))
  have himage (i : Index) : c i '' (K i).space =
      range (fun x : H.sourceSet i => (H.pieceCopy i x : P2)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, (hKs i).subset hx⟩, hcv i _⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (hKs i).symm.subset x.property, (hcv i x).symm⟩
  have hcover : (⋃ i, c i '' (K i).space) = T \ interior H.carrier := by
    simpa only [himage] using H.pieceCopy_cover
  obtain ⟨g, hg, hkeep, him, _⟩ :=
    exists_finite_copy_pasting e he K c hcK hci (pieceMap f τ) hfK hagree (f 0)
  refine ⟨g, hcover ▸ hg, ?_, ?_⟩
  · intro i x
    rw [hcv]
    exact hkeep i x ((hKs i).symm.subset x.property)
  · rw [hcover] at him
    simpa only [hKs] using him

end PoincareConjecture.M76.Dehn.NonspanningChainHole
