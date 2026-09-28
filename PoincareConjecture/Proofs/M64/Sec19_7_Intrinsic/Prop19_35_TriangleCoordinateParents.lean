import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleMatchedCore
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleBandCompatibility
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCapBandContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MatchedRegionParents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture.M64IntrinsicTriangleCollar

theorem exists_coordinate_parents
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∃ (m : ℕ) (F : Fin m → OpenPartialHomeomorph Plane AnnulusCoordinates)
      (basis : Fin m → AffineBasis (Fin 3) ℝ Plane),
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F p) (F p).source) ∧
      (∀ p, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F p).symm (F p).target) ∧
      (∀ p, convexHull ℝ (range (basis p)) ⊆ (F p).source) ∧
      (∀ p q, p ≠ q → CoordinateTriangleBoundaryIntersection
        (F p) (F q) (basis p) (basis q)) ∧
      (⋃ p, F p '' convexHull ℝ (range (basis p))) = closure U := by
  classical
  obtain ⟨Fcap, _, core, _, _, _, _, hrecover, hcorecap, hcoreband, _⟩ :=
    P.exists_matched_core hU hcompact hfront
  let occupied (e : Fin 3) (i : Bool × Bool) :=
    if C.positive e then i = (true, true) else i ≠ (true, true)
  let J := {p : Fin 3 × (Bool × Bool) // occupied p.1 p.2}
  let G : J → OpenPartialHomeomorph Plane AnnulusCoordinates :=
    fun j => Fcap.coordinates j.1.1 j.1.2
  let d : J → AffineBasis (Fin 3) ℝ Plane := fun j => Fcap.basis j.1.1 j.1.2
  have hface (e : Fin 3) (i : Bool × Bool) (hi : occupied e i) :
      (Fcap.face e i).carrier ⊆ C.carrier e := by
    rw [← Fcap.occupied_union e]
    exact fun _ hp => mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hp⟩⟩
  have hGG (j k : J) (hjk : j ≠ k) :
      CoordinateTriangleBoundaryIntersection (G j) (G k) (d j) (d k) := by
    rcases j with ⟨⟨e, i⟩, hi⟩
    rcases k with ⟨⟨f, j⟩, hj⟩
    by_cases hef : e = f
    · subst f
      exact Fcap.canonical e i j (fun h => hjk (Subtype.ext (congrArg (Prod.mk e) h)))
    · apply CoordinateTriangleBoundaryIntersection.disjoint
      change Disjoint (Fcap.coordinates e i '' convexHull ℝ (range (Fcap.basis e i)))
        (Fcap.coordinates f j '' convexHull ℝ (range (Fcap.basis f j)))
      rw [← Fcap.carrier, ← Fcap.carrier]
      exact (C.separated hef).mono (hface e i hi) (hface f j hj)
  have hchord (j : J) : G j '' affineSegment ℝ (d j ((0 : Fin 3).succAbove 0))
      (d j ((0 : Fin 3).succAbove 1)) = segment ℝ
        (C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (C.radius j.1.1, 0)))
        (C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (0, C.radius j.1.1))) := by
    dsimp only [G, d]
    rw [← Euler.affineChartSegment_image, ← image_comp, ← Fcap.boundary, segment_eq_image]
    exact image_congr (fun t _ => Fcap.chord j.1.1 j.1.2 t)
  have hcuts (i : P.BandIndex) (right : Bool) : ∃ u v : AnnulusCoordinates,
      ((P.bandData i).band.endpointEdge right).map '' Icc (0 : ℝ) 1 = segment ℝ u v := by
    rw [(P.bandData i).band.endpointEdge_image]
    cases right
    · exact ⟨_, _, m64Intrinsic_band_left_cut (P.bandData i).frame (P.bandData i).band⟩
    · exact ⟨_, _, m64Intrinsic_band_right_cut (P.bandData i).frame (P.bandData i).band⟩
  obtain ⟨m, F, basis, hF, hFi, hsource, hparents, hsupport⟩ :=
    m64Intrinsic_exists_cap_band_core_coordinate_parents
      (fun i =>
        (collarParameterEquiv.trans (P.bandData i).frame).toHomeomorph.toOpenPartialHomeomorph)
      (fun i => (P.bandData i).graph) (fun i => (P.bandData i).left)
      (fun i => (P.bandData i).right) (fun i => (P.bandData i).left_direction.1)
      (fun i => (P.bandData i).left_direction.2) (fun i => (P.bandData i).right_direction.1)
      (fun i => (P.bandData i).right_direction.2) (fun i => (P.bandData i).left_length)
      (fun i => (P.bandData i).right_length) (fun i => (P.bandData i).band)
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (P.bandData i).frame).contDiff.contDiffOn)
      (fun i => contMDiffOn_iff_contDiffOn.mpr
        (collarParameterEquiv.trans (P.bandData i).frame).symm.contDiff.contDiffOn)
      P.band_faces_canonical hcuts G d (fun j => Fcap.smooth j.1.1 j.1.2)
      (fun j => Fcap.inverse_smooth j.1.1 j.1.2) (fun j => Fcap.source j.1.1 j.1.2) hGG
      (fun _ => 0)
      (fun j => C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (C.radius j.1.1, 0)))
      (fun j => C.chart j.1.1 (sectorParameterEquiv 0 j.1.2 (0, C.radius j.1.1))) hchord
      (by
        intro i j p hp
        change p ∈ (P.bandData i).band.carrier ∩
          (Fcap.coordinates j.1.1 j.1.2 '' convexHull ℝ (range (Fcap.basis j.1.1 j.1.2))) at hp
        rw [← Fcap.carrier] at hp
        exact P.cap_band_outer j.1.1 i ⟨hface _ _ j.2 hp.2, hp.1⟩)
      (by
        intro i j p hp
        change p ∈ Fcap.coordinates j.1.1 j.1.2 '' affineSegment ℝ
          (Fcap.basis j.1.1 j.1.2 ((0 : Fin 3).succAbove 0))
          (Fcap.basis j.1.1 j.1.2 ((0 : Fin 3).succAbove 1))
        rw [← Euler.affineChartSegment_image, ← image_comp, ← Fcap.boundary]
        exact P.cap_face_band_chord hU Fcap j.1.1 j.1.2 j.2 i
          ⟨(Fcap.carrier _ _).symm.subset hp.2, hp.1⟩)
      core (fun t j => hcorecap j.1.1 j.1.2 j.2 t) (fun t i p => hcoreband i t p)
  have hchosen : (⋃ j : J, G j '' convexHull ℝ (range (d j))) = ⋃ e, C.carrier e := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hp⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨j.1.1, hface _ _ j.2 ((Fcap.carrier _ _).symm.subset hp)⟩
    · intro hp
      obtain ⟨e, hp⟩ := mem_iUnion.mp hp
      obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
      apply mem_iUnion.mpr
      refine ⟨⟨(e, i), hi⟩, ?_⟩
      change p ∈ Fcap.coordinates e i '' convexHull ℝ (range (Fcap.basis e i))
      rwa [← Fcap.carrier, Fcap.original_carrier]
  refine ⟨m, F, basis, hF, hFi, hsource, hparents, ?_⟩
  rw [hsupport, hchosen, P.band_union]
  simpa only [carrier, union_assoc] using hrecover.symm

end PoincareConjecture.M64IntrinsicTriangleCollar
