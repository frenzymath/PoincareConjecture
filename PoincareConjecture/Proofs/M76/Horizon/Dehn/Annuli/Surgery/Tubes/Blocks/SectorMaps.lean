import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalSectorMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.HalfFaceMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.SectorBoundary



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_local_sector_maps
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space C.chart.source)
    (hface : (D.complex.closedStar v).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar v).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0)
    (hsheet : ∀ j : Fin 2,
      ((D.complex.closedStar v).vertexSubcomplex
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
      (D.complex.closedStar v).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0})
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hdisj : Disjoint (D.complex.barycentricDualBlock (s false)).space
      (D.complex.barycentricDualBlock (s true)).space)
    (G : ∀ b, signedTubeDiamond ≃ₜ (D.complex.barycentricDualBlock (s b)).space)
    (hG : ∀ b, (G b).IsFinitePL)
    (hQ : ∀ b eps delta (z : signedTubeDiamond),
      (z : P2) ∈ signedTubeQuarter eps delta ↔
        (G b z : D.sample → ℝ × V3) ∈ signedCoordinateSector
          (D.complex.barycentricDualBlock (s b)).space
          (fun j w => C.chart (D.inverse w) j.castSucc) (fun _ => true) eps delta)
    (hcenter : ∀ b, (G b ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : D.sample → ℝ × V3) =
        (s b).centroid ℝ id) :
    let V := D.complex.barycentricDualBlock {v}
    let Z := V.space ∩ D.axis.space
    let face := fun (j : Fin 2) (sign : Bool) =>
      {z | z ∈ V.space ∧ C.chart (D.inverse z) j.castSucc = 0 ∧
        SignedJointCross.side sign (C.chart (D.inverse z) j.rev.castSucc)}
    ∃ (axis : Icc (0 : ℝ) 1 ≃ₜ Z)
      (halfMap : ∀ j sign, ↥(signedTubeRadius j sign ×ˢ Icc (0 : ℝ) 1) ≃ₜ face j sign),
      axis.IsFinitePL ∧ (∀ j sign, (halfMap j sign).IsFinitePL) ∧
      (∀ j sign (t : Icc (0 : ℝ) 1),
        (halfMap j sign ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : D.sample → ℝ × V3) = axis t) ∧
      ∀ signs : Fin 2 → Bool,
        let cuts := {z | ∀ j : Fin 2, SignedJointCross.side (signs j) (C.chart (D.inverse z) j.castSucc)}
        let boundary := {z | z ∈ V.space ∧ z ∈ cuts ∧
          (z ∈ (V.link v).space ∨ ∃ j : Fin 2, C.chart (D.inverse z) j.castSucc = 0)}
        ∃ map : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (0 : ℝ) 1) ≃ₜ ↥(V.space ∩ cuts),
          map.IsFinitePL ∧
          (∀ j (z : ↥(signedTubeRadius j (signs j.rev) ×ˢ Icc (0 : ℝ) 1)),
            (map ⟨z, signedTubeRadius_subset_quarter signs j z.property.1, z.property.2⟩ : D.sample → ℝ × V3) =
              halfMap j (signs j.rev) z) ∧
          (∀ b (z : signedTubeQuarter (signs 0) (signs 1)),
            (map ⟨(z, if b then 1 else 0), z.property, by cases b <;> simp⟩ : D.sample → ℝ × V3) =
              G b ⟨z, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, z.property⟩⟩⟩) ∧
          (∀ t : Icc (0 : ℝ) 1,
            (map ⟨((0, 0), t), signedTubeRadius_subset_quarter signs 0 (left_mem_segment ℝ _ _),
              t.property⟩ : D.sample → ℝ × V3) = axis t) ∧
          ∀ z : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc (0 : ℝ) 1),
            (z : P2 × ℝ) ∈ (signedTubeOuterArc (signs 0) (signs 1) ×ˢ Icc (0 : ℝ) 1) ∪
              signedTubeSectorPrescribed (signs 0) (signs 1) 0 1 ↔
                (map z : D.sample → ℝ × V3) ∈ boundary := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let Z := V.space ∩ D.axis.space
  let J := fun b => (D.complex.barycentricDualBlock (s b)).space
  let c := fun (j : Fin 2) z => C.chart (D.inverse z) j.castSucc
  let face := fun (j : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ c j z = 0 ∧ SignedJointCross.side sign (c j.rev z)}
  obtain ⟨axis, hAxis, _, _, hHalf⟩ := D.exists_local_half_face_maps hcore v hv C hC hface
    haxis s hs hcard hvs hdisj G hG hQ hcenter
  choose halfMap hHalfPL hAxisVal hEnd hAxisMem hOuterMem hEndMem using hHalf
  have hJV (b : Bool) : J b ⊆ V.space :=
    space_subset_of_le (D.complex.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (hvs b)))
  refine ⟨axis, halfMap, hAxis, hHalfPL, hAxisVal, ?_⟩
  intro signs
  let cuts := {z | ∀ j : Fin 2, SignedJointCross.side (signs j) (c j z)}
  let faces := fun j => face j (signs j.rev)
  let quarters := fun b => J b ∩ cuts
  let boundary := {z | z ∈ V.space ∧ z ∈ cuts ∧
    (z ∈ (V.link v).space ∨ ∃ j : Fin 2, c j z = 0)}
  have hQuarter (b : Bool) : ∃ qmap : signedTubeQuarter (signs 0) (signs 1) ≃ₜ quarters b,
      qmap.IsFinitePL ∧ ∀ z : signedTubeQuarter (signs 0) (signs 1),
        (qmap z : D.sample → ℝ × V3) =
          G b ⟨z, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, z.property⟩⟩⟩ := by
    apply exists_signed_diamond_quarter_restriction (G b) (hG b)
      (signs 0) (signs 1) inter_subset_left
    intro z
    simpa [signedCoordinateSector, signedCoordinateCut, signedTubeReindex, quarters,
      cuts, c, SignedJointCross.side, Fin.forall_fin_two] using hQ b (signs 0) (signs 1) z
  choose qmap hqmap hqval using hQuarter
  obtain ⟨rim, hDisk, hSub, hOut, hBall, _, hInter, _, hDisj⟩ :=
    D.exists_local_sector_boundary hcore v hv C hC hface haxis hsheet s hs hcard hvs hdisj signs
  have hA (z : ↥(signedTubeRadius 0 (signs 1) ×ˢ Icc (0 : ℝ) 1)) :
      (z : P2 × ℝ).1 = (0, 0) ↔ (halfMap 0 (signs 1) z : D.sample → ℝ × V3) ∈ Z := by
    simpa only [signedTubePrismAxis, mem_prod, mem_singleton_iff, z.property.2, and_true]
      using hAxisMem 0 (signs 1) z
  have hContact (b : Bool) (j : Fin 2) (z : signedTubeQuarter (signs 0) (signs 1)) :
      (qmap b z : D.sample → ℝ × V3) ∈ faces j ↔ (z : P2) ∈ signedTubeRadius j (signs j.rev) := by
    rw [hqval]
    let zd : signedTubeDiamond := ⟨z, mem_iUnion.mpr ⟨signs 0, mem_iUnion.mpr ⟨signs 1, z.property⟩⟩⟩
    have hzJ := (G b zd).property
    have hzV := hJV b hzJ
    have hi : (G b zd : D.sample → ℝ × V3) ∈ faces j ↔
        (G b zd : D.sample → ℝ × V3) ∈ signedCoordinateFace (J b) c (fun _ => true) j (signs j.rev) :=
      ⟨fun h => ⟨hzJ, h.2⟩, fun h => ⟨hzV, h.2⟩⟩
    exact hi.trans (signedDiamond_coordinate_radius_iff (J b) c (G b) (hQ b) j (signs j.rev) zd).symm
  have hKeep (j : Fin 2) (b : Bool) (z : signedTubeRadius j (signs j.rev)) :
      (halfMap j (signs j.rev) ⟨(z, if b then 1 else 0), z.property,
        by cases b <;> simp⟩ : D.sample → ℝ × V3) =
          qmap b ⟨z, signedTubeRadius_subset_quarter signs j z.property⟩ := by
    rw [hqval]
    exact hEnd j (signs j.rev) b z
  obtain ⟨map, hmap, hFace, hEndQuarter, hBoundary⟩ := exists_signed_sector_volume_map
    signs 0 1 zero_lt_one faces quarters Z _ _ rim hBall hDisk hSub hOut
      (fun j => halfMap j (signs j.rev)) qmap
      (fun j => hHalfPL j (signs j.rev)) hqmap hInter hDisj
      (fun t => (axis t : D.sample → ℝ × V3)) hA
      (fun j => hAxisVal j (signs j.rev)) hContact hKeep
  refine ⟨map, hmap, hFace, ?_, ?_, hBoundary⟩
  · intro b z
    exact (hEndQuarter b z).trans (hqval b z)
  · intro t
    exact (hFace 0 ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩).trans
      (hAxisVal 0 (signs 1) t)

end PoincareConjecture.M76.Dehn.Annuli
