import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierSourceGraph
import PoincareConjecture.Proofs.M76.Triangulation.OrientedQuadrantFrontierMap












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_actual_surface_frontier_map
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C S d : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hKC : K.space = C) (hzero : (0 : E) ∈ interior C)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hdim : Module.finrank ℝ E = 3)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hPS : P.boundary ℝ = frontier C ∩ S)
    (p : Bool → E) (hp : p false ≠ p true)
    (hPzero : P.boundary ℝ ∩ {x | A x = 0} = {p false, p true})
    (hnegP : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hposP : ∃ x ∈ P.boundary ℝ, 0 < A x)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (ψ : Bool → (ℝ × ℝ) → E) (hinj : ∀ j, Function.Injective (ψ j))
    (hψzero : ∀ j, ψ j 0 = p j) (r : Bool → ℝ) (hr : ∀ j, 0 < r j)
    (hheight : ∀ j x, A (ψ j x) = x.1)
    (hSource : ∀ (i : Bool × Bool) (j : Bool),
      SourcePoleQuadrantData (ψ j) (frontier C) S
        (frontier C ∩ (S ∪ {x | A x = 0})) (p j) (p (!j)) A
        (if i.1 then -r j else r j) (if i.2 then -r j else r j))
    (δ : Bool → ℝ) (hδ : ∀ j, 0 < δ j)
    (hside : ∀ j z, |z| ≤ δ j → (ψ j (0, z) ∈ d ↔ 0 ≤ z))
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hfirst : ∀ j x, (L j (ψ j x)).1.1 = x.1)
    (hlast : ∀ j x, (L j (ψ j x)).2 = x.2)
    (T : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hT : T.faces.Finite)
    {D : Set ((ℝ × ℝ) × ℝ)} (hD : IsCompact D) (hDcv : Convex ℝ D)
    (hTD : T.space = D) (hDzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior D)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hLp : ∀ j, L j (p j) = ((0, σ j), 0))
    (hpD : ∀ j, L j (p j) ∈ frontier D)
    (hTargetSquare : ∀ j, L j '' (ψ j '' base (r j)) ⊆ frontier D)
    (hdis : Disjoint (ψ false '' base (r false)) (ψ true '' base (r true)))
    (hDis : Disjoint (L false '' (ψ false '' base (r false)))
      (L true '' (ψ true '' base (r true)))) :
    ∃ H : frontier C ≃ₜ frontier D, H.IsFinitePL ∧
      (∀ i j (x : frontier C), (x : E) ∈ ψ j '' signedRectangle (r j) i →
        (H x : (ℝ × ℝ) × ℝ) = L j x) ∧
      (∀ x : frontier C, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      (∀ x : frontier C, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0) ∧
      ∀ x : frontier C, (x : E) ∈ S ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  have hPC : P.boundary ℝ ⊆ frontier C := hPS.subset.trans inter_subset_left
  obtain ⟨arc, disk, hArc, hArcInter, hDisk, hcontact, hpair, hwhole,
    hgraph, hequator, hlink, hheightUnion⟩ :=
    K.exists_convex_frontier_source_graph hK hC hcv hKC hdim A.toAffineMap
      hzero (map_zero A) P hP hinjP hPC hp hPzero hnegP hposP
  have hphysical : (⋃ i, arc i) = frontier C ∩ (S ∪ {x | A x = 0}) := by
    rw [hgraph, hPS]
    ext x
    simp only [mem_inter_iff, mem_union, mem_ofPred_eq]
    tauto
  have hlink' (i : Bool) : arc (true, i) =
      (frontier C ∩ S) ∩ {x | CoordinateFourRegions.weakSign i (A x)} := by
    rw [hlink i, hPS]
    rfl
  have hSource' (i : Bool × Bool) (j : Bool) :
      SourcePoleQuadrantData (ψ j) (frontier C) S (⋃ k, arc k) (p j) (p (!j)) A
        (if i.1 then -r j else r j) (if i.2 then -r j else r j) := by
    rw [hphysical]
    exact hSource i j
  exact exists_oriented_quadrant_frontier_map A hA hdim arc disk p hp hArc hArcInter
    hDisk hcontact hpair hwhole hequator hlink' hheightUnion hd hdplane ψ hinj hψzero
    r hr hheight hSource' δ hδ hside L hfirst hlast T hT hD hDcv hTD hDzero σ
    hσneg hσpos hLp hpD hTargetSquare hdis hDis

end Geometry.SimplicialComplex
