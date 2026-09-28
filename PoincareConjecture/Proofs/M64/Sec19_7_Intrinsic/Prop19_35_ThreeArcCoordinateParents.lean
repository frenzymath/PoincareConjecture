import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcMatchedCore
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcBandCompatibility
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapBandContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MatchedRegionParents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture.M64IntrinsicThreeArcCollar

theorem exists_coordinate_parents
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
    (D : M64IntrinsicThreeArcCollar C b)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∃ (m : ℕ) (F : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (basis : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F p) (F p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F p).symm (F p).target) ∧
      (∀ p, convexHull ℝ (range (basis p)) ⊆ (F p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection
        (F p) (F q) (basis p) (basis q)) ∧
      (⋃ p, F p '' convexHull ℝ (range (basis p))) = closure U := by
  classical
  obtain ⟨A, _, core, _, _, _, _, hrecover, hcorecap, hcoreband, _⟩ :=
    D.exists_matched_core hU hcompact hfront
  let occupied (e : Bool) (i : Bool × Bool) :=
    if C.positive e then i = (true, true) else i ≠ (true, true)
  let J := {p : Bool × (Bool × Bool) // occupied p.1 p.2}
  let G : J → OpenPartialHomeomorph Plane AnnulusCoordinates := fun j => A.coordinates j.1.1 j.1.2
  let d : J → AffineBasis (Fin 3) ℝ Plane := fun j => A.basis j.1.1 j.1.2
  have hface (e : Bool) (i : Bool × Bool) (hi : occupied e i) :
      (A.face e i).carrier ⊆ C.carrier e := by
    rw [← A.occupied_union e]
    exact fun _ hp => mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp⟩⟩
  have hGG (j k : J) (hjk : j ≠ k) :
      CoordinateTriangleBoundaryIntersection (G j) (G k) (d j) (d k) := by
    rcases j with ⟨⟨e, i⟩, hi⟩
    rcases k with ⟨⟨f, j⟩, hj⟩
    by_cases hef : e = f
    · subst f
      exact A.canonical e i j (fun h => hjk (Subtype.ext (congrArg (Prod.mk e) h)))
    · apply CoordinateTriangleBoundaryIntersection.disjoint
      change Disjoint (A.coordinates e i '' convexHull ℝ (range (A.basis e i)))
        (A.coordinates f j '' convexHull ℝ (range (A.basis f j)))
      rw [← A.carrier, ← A.carrier]
      exact (C.disjoint_of_ne e f hef).mono (hface e i hi) (hface f j hj)
  have hchord (j : J) : G j '' affineSegment ℝ (d j ((0 : Fin 3).succAbove 0))
      (d j ((0 : Fin 3).succAbove 1)) = segment ℝ
        (C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (C.radius j.1.1, 0)))
        (C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (0, C.radius j.1.1))) := by
    dsimp only [G, d]
    rw [← Euler.affineChartSegment_image, ← image_comp, ← A.boundary, segment_eq_image]
    exact image_congr (fun t _ => A.chord j.1.1 j.1.2 t)
  have hcuts (i : D.BandIndex) (right : Bool) : ∃ u v : AnnulusCoordinates,
      ((D.bandData i).band.endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v := by
    rw [(D.bandData i).band.endpointEdge_image]
    cases right
    · exact ⟨_, _, m64Intrinsic_band_left_cut (D.bandData i).frame (D.bandData i).band⟩
    · exact ⟨_, _, m64Intrinsic_band_right_cut (D.bandData i).frame (D.bandData i).band⟩
  obtain ⟨m, F, basis, hF, hFi, hsource, hparents, hsupport⟩ :=
    m64Intrinsic_exists_cap_band_core_coordinate_parents
      (fun i =>
        (collarParameterEquiv.trans (D.bandData i).frame).toHomeomorph.toOpenPartialHomeomorph)
      (fun i => (D.bandData i).graph) (fun i => (D.bandData i).left)
      (fun i => (D.bandData i).right) (fun i => (D.bandData i).left_direction.1)
      (fun i => (D.bandData i).left_direction.2) (fun i => (D.bandData i).right_direction.1)
      (fun i => (D.bandData i).right_direction.2) (fun i => (D.bandData i).left_length)
      (fun i => (D.bandData i).right_length) (fun i => (D.bandData i).band)
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (D.bandData i).frame).contDiff.contDiffOn)
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (D.bandData i).frame).symm.contDiff.contDiffOn)
      D.band_faces_canonical hcuts G d (fun j => A.smooth j.1.1 j.1.2)
      (fun j => A.inverse_smooth j.1.1 j.1.2) (fun j => A.source j.1.1 j.1.2) hGG
      (fun _ => 0)
      (fun j => C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (C.radius j.1.1, 0)))
      (fun j => C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (0, C.radius j.1.1))) hchord
      (by
        intro i j p hp
        change p ∈ (D.bandData i).band.carrier ∩
          (A.coordinates j.1.1 j.1.2 '' convexHull ℝ (range (A.basis j.1.1 j.1.2))) at hp
        rw [← A.carrier] at hp
        exact D.cap_band_outer j.1.1 i ⟨hface _ _ j.2 hp.2, hp.1⟩)
      (by
        intro i j p hp
        change p ∈ A.coordinates j.1.1 j.1.2 '' affineSegment ℝ
          (A.basis j.1.1 j.1.2 ((0 : Fin 3).succAbove 0))
          (A.basis j.1.1 j.1.2 ((0 : Fin 3).succAbove 1))
        rw [← Euler.affineChartSegment_image, ← image_comp, ← A.boundary]
        exact D.cap_face_band_chord hU A j.1.1 j.1.2 j.2 i
          ⟨(A.carrier _ _).symm.subset hp.2, hp.1⟩)
      core (fun t j => hcorecap j.1.1 j.1.2 j.2 t) (fun t i p => hcoreband i t p)
  have hchosen : (⋃ j : J, G j '' convexHull ℝ (range (d j))) =
      C.carrier false ∪ C.carrier true := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hp⟩ := mem_iUnion.mp hp
      have h : p ∈ C.carrier j.1.1 := hface _ _ j.2 ((A.carrier _ _).symm.subset hp)
      cases he : j.1.1
      · exact Or.inl (by simpa only [he] using h)
      · exact Or.inr (by simpa only [he] using h)
    · rintro (hp | hp)
      · obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
        apply mem_iUnion.mpr
        refine ⟨⟨(false, i), hi⟩, ?_⟩
        change p ∈ A.coordinates false i '' convexHull ℝ (range (A.basis false i))
        rwa [← A.carrier, A.original_carrier]
      · obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
        apply mem_iUnion.mpr
        refine ⟨⟨(true, i), hi⟩, ?_⟩
        change p ∈ A.coordinates true i '' convexHull ℝ (range (A.basis true i))
        rwa [← A.carrier, A.original_carrier]
  refine ⟨m, F, basis, hF, hFi, hsource, hparents, ?_⟩
  rw [hsupport, hchosen, D.band_union]
  simpa only [carrier, union_assoc] using hrecover.symm

end PoincareConjecture.M64IntrinsicThreeArcCollar
