import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleRegionAttachments
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFourDiskGluing
import PoincareConjecture.Proofs.M76.Mathlib.CanonicalAxisArcMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearGraphExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearRegionExtension
import PoincareConjecture.Proofs.M76.Mathlib.MarkedRegionMapSigns
import PoincareConjecture.Proofs.M76.Mathlib.SignedQuadrantPatchRetention












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes RectangleCornerArcs

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_prescribed_quadrant_frontier_map
    {F S : Set E} {T : Set ((ℝ × ℝ) × ℝ)}
    (sourceArc disk : Bool × Bool → Set E) (p : Bool → E)
    (ψ : Bool → (ℝ × ℝ) → E) (r : Bool → ℝ) (hr : ∀ j, 0 < r j)
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (A : E →ₗ[ℝ] ℝ)
    (hp : p false ≠ p true) (hLp : L false (p false) ≠ L true (p true))
    (hArc : ∀ i, IsFinitePLBallPair ℝ (sourceArc i) {p false, p true})
    (hArcInter : Pairwise (fun i j => sourceArc i ∩ sourceArc j = {p false, p true}))
    (hDisk : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (disk i)
      (sourceArc (false, i.2) ∪ sourceArc (true, i.1)))
    (hcontact : ∀ i, disk i ∩ (⋃ k, sourceArc k) =
      sourceArc (false, i.2) ∪ sourceArc (true, i.1))
    (hpair : Pairwise (fun i j => disk i ∩ disk j ⊆ ⋃ k, sourceArc k))
    (hwhole : (⋃ i, disk i) = F)
    (hlink : ∀ i : Bool, sourceArc (true, i) =
      (F ∩ S) ∩ {x | if i then A x ≤ 0 else 0 ≤ A x})
    (hheightUnion : ∀ i : Bool, disk (i, false) ∪ disk (i, true) =
      F ∩ {x | CoordinateFourRegions.weakSign i (A x)})
    (hTargetArc : ∀ i, IsFinitePLBallPair ℝ (CoordinateFourRegions.arc T i)
      {L false (p false), L true (p true)})
    (hTargetArcInter : Pairwise (fun i j =>
      CoordinateFourRegions.arc T i ∩ CoordinateFourRegions.arc T j =
        {L false (p false), L true (p true)}))
    (hTargetDisk : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (CoordinateFourRegions.region T i)
      (CoordinateFourRegions.arc T (false, i.2) ∪ CoordinateFourRegions.arc T (true, i.1)))
    (hheight : ∀ j (x : ℝ × ℝ), A (ψ j x) = x.1)
    (hSource : ∀ (i : Bool × Bool) (j : Bool),
      SourcePoleQuadrantData (ψ j) F S (⋃ k, sourceArc k) (p j) (p (!j)) A
        (if i.1 then -r j else r j) (if i.2 then -r j else r j))
    (hTarget : ∀ (i : Bool × Bool) (j : Bool),
      LinearImageQuadrantData (ψ j) (L j) T (p j)
        (if i.1 then -r j else r j) (if i.2 then -r j else r j) i)
    (hvertical : ∀ (i j : Bool),
      ψ j '' ({0} ×ˢ uIcc 0 (if i then -r j else r j)) ⊆ sourceArc (false, i))
    (hdis : Disjoint (ψ false '' base (r false)) (ψ true '' base (r true)))
    (hDis : Disjoint (L false '' (ψ false '' base (r false)))
      (L true '' (ψ true '' base (r true)))) :
    ∃ H : F ≃ₜ T, H.IsFinitePL ∧
      (∀ i j (x : F), (x : E) ∈ ψ j '' signedRectangle (r j) i →
        (H x : (ℝ × ℝ) × ℝ) = L j x) ∧
      (∀ i (x : F), (x : E) ∈ disk i ↔
        (H x : (ℝ × ℝ) × ℝ) ∈ CoordinateFourRegions.region T i) ∧
      (∀ i (x : F), (x : E) ∈ sourceArc i ↔
        (H x : (ℝ × ℝ) × ℝ) ∈ CoordinateFourRegions.arc T i) ∧
      (∀ x : F, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      (∀ x : F, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0) ∧
      ∀ x : F, (x : E) ∈ S ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  classical
  let a : Bool → (ℝ × ℝ) × ℝ := fun j => L j (p j)
  let ends : (Bool × Bool) → Bool → Set E := fun i j =>
    ψ j '' axisInterval i.1 (if i.2 then -r j else r j)
  let tip : (Bool × Bool) → Bool → E := fun i j => ψ j
    (if i.1 then (if i.2 then -r j else r j, 0)
      else (0, if i.2 then -r j else r j))
  have hsign (i j : Bool) :
      if i then (if i then -r j else r j) ≤ 0 else 0 ≤ (if i then -r j else r j) := by
    cases i
    · exact (hr j).le
    · exact neg_nonpos.mpr (hr j).le
  have hEndPair (i : Bool × Bool) (j : Bool) :
      IsFinitePLBallPair ℝ (ends i j) {p j, tip i j} := by
    rcases i with ⟨k, b⟩
    cases k
    · exact (hSource (false, b) j).vertical
    · exact (hSource (b, false) j).horizontal
  have hEndSource (i : Bool × Bool) (j : Bool) : ends i j ⊆ sourceArc i := by
    rcases i with ⟨k, b⟩
    cases k
    · exact hvertical b j
    · exact (hSource (b, false) j).horizontal_axis_subset_signed_arc
        sourceArc hlink (hheight j) b (hsign b j)
  have hEndTarget (i : Bool × Bool) (j : Bool) :
      L j '' ends i j ⊆ CoordinateFourRegions.arc T i := by
    rcases i with ⟨k, b⟩
    cases k
    · exact (hTarget (false, b) j).vertical_arc
    · exact (hTarget (b, false) j).horizontal_arc
  have hEndNe (i : Bool × Bool) (j : Bool) : p j ≠ tip i j := by
    rcases i with ⟨k, b⟩
    cases k
    · intro heq
      exact (hSource (false, b) j).vertical_endpoint.2 (Or.inl heq.symm)
    · intro heq
      exact (hSource (b, false) j).horizontal_endpoint.2 (Or.inl heq.symm)
  have hEndSquare (i : Bool × Bool) (j : Bool) : ends i j ⊆ ψ j '' base (r j) := by
    apply image_mono
    apply axisInterval_subset_base i.1 (hr j).le
    cases i.2 <;> simp [abs_of_pos (hr j)]
  have hEndDis (i : Bool × Bool) : Disjoint (ends i false) (ends i true) :=
    hdis.mono (hEndSquare i false) (hEndSquare i true)
  have hEndDis' (i : Bool × Bool) :
      Disjoint (L false '' ends i false) (L true '' ends i true) :=
    hDis.mono (image_mono (hEndSquare i false)) (image_mono (hEndSquare i true))
  obtain ⟨G, hG, hGkeep, hGArc, _, _, _⟩ :=
    exists_finitePL_marked_graph_with_linear_ends sourceArc (CoordinateFourRegions.arc T)
      ends p a tip L hArc hTargetArc hArcInter hTargetArcInter hEndPair hEndSource
      hEndTarget hp hLp hEndNe hEndDis hEndDis' (fun _ => rfl)
  let d : (Bool × Bool) → Bool → Set E := fun i j => ψ j '' signedRectangle (r j) i
  let u : (Bool × Bool) → Bool → Set E := fun i j =>
    ψ j '' cornerArc 0 (if i.1 then -r j else r j) 0 (if i.2 then -r j else r j)
  let w : (Bool × Bool) → Bool → Set E := fun i j =>
    ψ j '' cornerArc (if i.1 then -r j else r j) 0 (if i.2 then -r j else r j) 0
  let b : (Bool × Bool) → Bool → E := fun i j => ψ j (0, if i.2 then -r j else r j)
  let c : (Bool × Bool) → Bool → E := fun i j => ψ j (if i.1 then -r j else r j, 0)
  have hArcAt (j : Bool) : Pairwise (fun k l =>
      sourceArc k ∩ sourceArc l = {p j, p (!j)}) := by
    intro k l hkl
    rw [hArcInter hkl]
    cases j
    · rfl
    · exact pair_comm _ _
  have hdSource (i : Bool × Bool) (j : Bool) : d i j ⊆ disk i := by
    apply ((hSource i j).attached_to_labelled_region sourceArc disk (hArcAt j) hDisk
      hwhole.symm.subset rfl hpair hcontact hlink
      (hheight j (if i.1 then -r j else r j, 0)) i (hsign i.1 j) ?_).1
    exact hvertical i.2 j
      ⟨(0, if i.2 then -r j else r j), ⟨rfl, right_mem_uIcc⟩, rfl⟩
  have hdSquare (i : Bool × Bool) (j : Bool) : d i j ⊆ ψ j '' base (r j) := by
    apply image_mono
    rw [base_eq_iUnion_signedRectangle (hr j).le]
    exact subset_iUnion (signedRectangle (r j)) i
  have hdDis (i : Bool × Bool) : Disjoint (d i false) (d i true) :=
    hdis.mono (hdSquare i false) (hdSquare i true)
  have hdDis' (i : Bool × Bool) :
      Disjoint (L false '' d i false) (L true '' d i true) :=
    hDis.mono (image_mono (hdSquare i false)) (image_mono (hdSquare i true))
  have hGraphCover : (⋃ k, sourceArc k) ⊆ ⋃ i, disk i := by
    intro x hx
    obtain ⟨⟨k, l⟩, hxl⟩ := mem_iUnion.mp hx
    cases k
    · exact mem_iUnion.mpr ⟨(false, l), (hDisk (false, l)).1 (Or.inl hxl)⟩
    · exact mem_iUnion.mpr ⟨(l, false), (hDisk (l, false)).1 (Or.inr hxl)⟩
  obtain ⟨hTcontact, hTpair, hTcover⟩ := four_disk_graph_contacts
    (CoordinateFourRegions.arc T) (CoordinateFourRegions.region T)
    (fun i => (hTargetDisk i).1) (CoordinateFourRegions.region_contacts T)
  have hGmem (i : Bool × Bool) (x : ⋃ k, sourceArc k) :
      (x : E) ∈ sourceArc (false, i.2) ∪ sourceArc (true, i.1) ↔
        (G x : (ℝ × ℝ) × ℝ) ∈ CoordinateFourRegions.arc T (false, i.2) ∪
          CoordinateFourRegions.arc T (true, i.1) :=
    or_congr (hGArc (false, i.2) x) (hGArc (true, i.1) x)
  have hdgraph (i : Bool × Bool) (j : Bool) : d i j ∩ (⋃ k, sourceArc k) = u i j :=
    (hSource i j).graph_contact
  have hDgraph (i : Bool × Bool) (j : Bool) :
      (L j '' d i j) ∩ (⋃ k, CoordinateFourRegions.arc T k) = L j '' u i j := by
    rw [CoordinateFourRegions.iUnion_arc]
    exact (hTarget i j).graph_contact
  have hGL (i : Bool × Bool) (j : Bool) (x : u i j) :
      (G ⟨x, ((hdgraph i j).symm.subset x.property).2⟩ : (ℝ × ℝ) × ℝ) = L j x := by
    rcases x with ⟨x, ⟨v, hv, rfl⟩⟩
    rcases hv with hv | hv
    · exact hGkeep (false, i.2) j ⟨ψ j v, ⟨v, hv, rfl⟩⟩
    · exact hGkeep (true, i.1) j ⟨ψ j v, ⟨v, hv, rfl⟩⟩
  obtain ⟨H₀, hH₀, hkeep, hgraph, hregions, _⟩ :=
    exists_finitePL_linear_region_gluing disk
      (fun i => sourceArc (false, i.2) ∪ sourceArc (true, i.1))
      (CoordinateFourRegions.region T)
      (fun i => CoordinateFourRegions.arc T (false, i.2) ∪ CoordinateFourRegions.arc T (true, i.1))
      hDisk hTargetDisk hcontact hTcontact hpair hTpair hGraphCover hTcover G hG hGmem
      d u w b c L (fun i j => (hSource i j).disk) hdSource
      (fun i j => (hTarget i j).region_subset) (fun i j => (hSource i j).inner)
      (fun i j => (hSource i j).outer) (fun i j => (hSource i j).endpoint_ne)
      (fun i j => (hSource i j).corner_inter) hdgraph hDgraph hdDis hdDis' hGL
  have hArcs := H₀.mem_marked_subsets_of_extension G hGraphCover hTcover hgraph
    sourceArc (CoordinateFourRegions.arc T) (subset_iUnion sourceArc)
    (subset_iUnion (CoordinateFourRegions.arc T)) hGArc
  let H : F ≃ₜ T := (Homeomorph.setCongr hwhole.symm).trans
    (H₀.trans (Homeomorph.setCongr (CoordinateFourRegions.iUnion_region T)))
  have hH : H.IsFinitePL := hH₀.setCongr hwhole (CoordinateFourRegions.iUnion_region T)
  have hregions' (i : Bool × Bool) (x : F) :
      (x : E) ∈ disk i ↔ (H x : (ℝ × ℝ) × ℝ) ∈ CoordinateFourRegions.region T i :=
    hregions i ⟨x, hwhole.symm.subset x.property⟩
  have hArcs' (i : Bool × Bool) (x : F) :
      (x : E) ∈ sourceArc i ↔ (H x : (ℝ × ℝ) × ℝ) ∈ CoordinateFourRegions.arc T i :=
    hArcs i ⟨x, hwhole.symm.subset x.property⟩
  have hlinkUnion : sourceArc (true, false) ∪ sourceArc (true, true) = F ∩ S := by
    rw [hlink false, hlink true]
    ext x
    constructor
    · exact fun hx => hx.elim (fun h => h.1) (fun h => h.1)
    · intro hx
      exact (le_total 0 (A x)).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  obtain ⟨hpositive, hnegative, hplane⟩ := H.coordinate_signs_of_marked_regions
    disk sourceArc A hheightUnion hlinkUnion hregions' hArcs'
  refine ⟨H, hH, ?_, hregions', hArcs', hpositive, hnegative, ?_⟩
  · intro i j x hx
    exact hkeep i j ⟨x, hx⟩
  · intro x
    exact ⟨fun hx => (hplane x).mp ⟨x.property, hx⟩,
      fun hx => ((hplane x).mpr hx).2⟩

end Geometry
