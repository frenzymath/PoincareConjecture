import PoincareConjecture.Proofs.M76.Triangulation.PrescribedQuadrantFrontierMap
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierCoordinateDiagram
import PoincareConjecture.Proofs.M76.Mathlib.MarkedEquatorRelabeling
import PoincareConjecture.Proofs.M76.Mathlib.BoundedDiskSourcePoleLabels

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes CoordinateFourRegions

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_oriented_quadrant_frontier_map
    {F S d : Set E} (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hdim : Module.finrank ℝ E = 3)
    (sourceArc disk : Bool × Bool → Set E) (p : Bool → E)
    (hp : p false ≠ p true)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (sourceArc i) {p false, p true})
    (hArcInter : Pairwise (fun i j => sourceArc i ∩ sourceArc j = {p false, p true}))
    (hDisk : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (disk i)
      (sourceArc (false, i.2) ∪ sourceArc (true, i.1)))
    (hcontact : ∀ i, disk i ∩ (⋃ k, sourceArc k) =
      sourceArc (false, i.2) ∪ sourceArc (true, i.1))
    (hpair : Pairwise (fun i j => disk i ∩ disk j ⊆ ⋃ k, sourceArc k))
    (hwhole : (⋃ i, disk i) = F)
    (hequator : sourceArc (false, false) ∪ sourceArc (false, true) =
      F ∩ {x | A x = 0})
    (hlink : ∀ i : Bool, sourceArc (true, i) = (F ∩ S) ∩ {x | weakSign i (A x)})
    (hheightUnion : ∀ i : Bool, disk (i, false) ∪ disk (i, true) =
      F ∩ {x | weakSign i (A x)})
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (ψ : Bool → (ℝ × ℝ) → E) (hinj : ∀ j, Function.Injective (ψ j))
    (hψzero : ∀ j, ψ j 0 = p j) (r : Bool → ℝ) (hr : ∀ j, 0 < r j)
    (hheight : ∀ j x, A (ψ j x) = x.1)
    (hSource : ∀ (i : Bool × Bool) (j : Bool),
      SourcePoleQuadrantData (ψ j) F S (⋃ k, sourceArc k) (p j) (p (!j)) A
        (if i.1 then -r j else r j) (if i.2 then -r j else r j))
    (δ : Bool → ℝ) (hδ : ∀ j, 0 < δ j)
    (hside : ∀ j z, |z| ≤ δ j → (ψ j (0, z) ∈ d ↔ 0 ≤ z))
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hfirst : ∀ j x, (L j (ψ j x)).1.1 = x.1)
    (hlast : ∀ j x, (L j (ψ j x)).2 = x.2)
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    {D : Set ((ℝ × ℝ) × ℝ)} (hD : IsCompact D) (hDcv : Convex ℝ D)
    (hKD : K.space = D) (hDzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior D)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hLp : ∀ j, L j (p j) = ((0, σ j), 0))
    (hpD : ∀ j, L j (p j) ∈ frontier D)
    (hTargetSquare : ∀ j, L j '' (ψ j '' base (r j)) ⊆ frontier D)
    (hdis : Disjoint (ψ false '' base (r false)) (ψ true '' base (r true)))
    (hDis : Disjoint (L false '' (ψ false '' base (r false)))
      (L true '' (ψ true '' base (r true)))) :
    ∃ H : F ≃ₜ frontier D, H.IsFinitePL ∧
      (∀ i j (x : F), (x : E) ∈ ψ j '' signedRectangle (r j) i →
        (H x : (ℝ × ℝ) × ℝ) = L j x) ∧
      (∀ x : F, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      (∀ x : F, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0) ∧
      ∀ x : F, (x : E) ∈ S ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  obtain ⟨j, _, _, hlabels⟩ := exists_common_source_pole_equator_labels A hA hdim
    hd hdplane sourceArc p hp hArc hArcInter hequator hlink ψ hinj hψzero r hr
    (fun k => hSource (false, true) k) (fun k => hSource (false, false) k) δ hδ hside
  obtain ⟨arc', disk', _, _, _, hgraph, hArc', hArcInter', hDisk', hcontact',
    hpair', hwhole', hlink', hheightUnion', hvertical⟩ :=
    exists_marked_graph_with_signed_vertical_labels sourceArc disk (p false) (p true) A
      hArc hArcInter hDisk hcontact hpair hwhole hlink hheightUnion ψ r j
      (fun k => (hlabels k).1) (fun k => (hlabels k).2)
  have hSource' (i : Bool × Bool) (k : Bool) :
      SourcePoleQuadrantData (ψ k) F S (⋃ l, arc' l) (p k) (p (!k)) A
        (if i.1 then -r k else r k) (if i.2 then -r k else r k) := by
    rw [hgraph]
    exact hSource i k
  have hpD' (k : Bool) : ((0, σ k), 0) ∈ frontier D := hLp k ▸ hpD k
  obtain ⟨hTargetArc, hTargetArcInter, hTargetDisk, _, _, _, _⟩ :=
    K.coordinate_frontier_marked_diagram hK hD hDcv hKD hDzero
      hσneg hσpos (hpD' false) (hpD' true)
  have hTargetArc' (i : Bool × Bool) :
      IsFinitePLBallPair ℝ (arc (frontier D) i) {L false (p false), L true (p true)} := by
    simpa only [hLp false, hLp true] using hTargetArc i
  have hTargetArcInter' : Pairwise (fun i k =>
      arc (frontier D) i ∩ arc (frontier D) k = {L false (p false), L true (p true)}) := by
    simpa only [hLp false, hLp true] using hTargetArcInter
  have hLpne : L false (p false) ≠ L true (p true) := by
    intro heq
    have hscalar := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) heq
    have hsig : σ false = σ true := by simpa only [hLp false, hLp true] using hscalar
    exact (ne_of_lt (hσneg.trans hσpos)) hsig
  have hsign (i k : Bool) : weakSign i (if i then -r k else r k) := by
    cases i
    · exact (hr k).le
    · exact neg_nonpos.mpr (hr k).le
  have hTarget (i : Bool × Bool) (k : Bool) :
      LinearImageQuadrantData (ψ k) (L k) (frontier D) (p k)
        (if i.1 then -r k else r k) (if i.2 then -r k else r k) i := by
    apply (hSource i k).linear_image_coordinate_attachment (L k) (frontier D)
      (hfirst k) (hlast k) ?_ i (hsign i.1 k) (hsign i.2 k)
    apply Subset.trans (image_mono (image_mono ?_)) (hTargetSquare k)
    change signedRectangle (r k) i ⊆ base (r k)
    rw [base_eq_iUnion_signedRectangle (hr k).le]
    exact subset_iUnion (signedRectangle (r k)) i
  obtain ⟨H, hH, hkeep, _, _, hpos, hneg, hplane⟩ :=
    exists_prescribed_quadrant_frontier_map arc' disk' p ψ r hr L A hp hLpne
      hArc' hArcInter' hDisk' hcontact' hpair' hwhole' hlink' hheightUnion'
      hTargetArc' hTargetArcInter' hTargetDisk hheight hSource' hTarget hvertical hdis hDis
  exact ⟨H, hH, hkeep, hpos, hneg, hplane⟩

end Geometry
