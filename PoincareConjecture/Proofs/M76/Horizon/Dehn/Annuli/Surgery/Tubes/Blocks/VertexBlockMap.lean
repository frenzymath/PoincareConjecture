import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalVertexBlockMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.SectorMaps



set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_local_vertex_block_map
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
    ∃ (axis : Icc (0 : ℝ) 1 ≃ₜ Z)
      (map : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ V.space),
      axis.IsFinitePL ∧ map.IsFinitePL ∧
      (∀ b (z : signedTubeDiamond),
        (map ⟨(z, if b then 1 else 0), z.property, by cases b <;> simp⟩ : D.sample → ℝ × V3) = G b z) ∧
      (∀ t : Icc (0 : ℝ) 1,
        (map ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
          (left_mem_segment ℝ _ _), t.property⟩ : D.sample → ℝ × V3) = axis t) ∧
      (∀ eps delta (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
        (z : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
          (map z : D.sample → ℝ × V3) ∈ V.space ∩ {w | ∀ j : Fin 2,
            if (![eps, delta] j) then 0 ≤ C.chart (D.inverse w) j.castSucc
              else C.chart (D.inverse w) j.castSucc ≤ 0}) ∧
      (∀ j (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
        (z : P2 × ℝ).1 ∈ signedTubeSheet j ↔ C.chart (D.inverse (map z)) j.castSucc = 0) ∧
      (∀ z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1),
        (z : P2 × ℝ).1 = (0, 0) ↔ (map z : D.sample → ℝ × V3) ∈ D.axis.space) ∧
      ∀ b (z : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
        (map z : D.sample → ℝ × V3) ∈ (D.complex.barycentricDualBlock (s b)).space ↔
          (z : P2 × ℝ).2 = if b then 1 else 0 := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let Z := V.space ∩ D.axis.space
  let coords := fun (j : Fin 2) z => C.chart (D.inverse z) j.castSucc
  let sector := fun eps delta : Bool => V.space ∩ {z | ∀ j : Fin 2,
    if (![eps, delta] j) then 0 ≤ coords j z else coords j z ≤ 0}
  let face := fun (j : Fin 2) (sign : Bool) =>
    {z | z ∈ V.space ∧ coords j z = 0 ∧ SignedJointCross.side sign (coords j.rev z)}
  obtain ⟨axis, halfMap, hAxis, _, _, hSectors⟩ := D.exists_local_sector_maps hcore v hv C
    hC hface haxis hsheet s hs hcard hvs hdisj G hG hQ hcenter
  have hSector (eps delta : Bool) : sector eps delta =
      signedCoordinateSector V.space coords (fun _ => true) eps delta := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, hz.2 0, hz.2 1⟩
    · rintro ⟨hd, h0, h1⟩
      refine ⟨hd, ?_⟩
      intro j
      fin_cases j
      · exact h0
      · exact h1
  have hFace (j : Fin 2) (sign : Bool) : face j sign =
      signedCoordinateFace V.space coords (fun _ => true) j sign := rfl
  have hAxisEq : {z | z ∈ V.space ∧ coords 0 z = 0 ∧ coords 1 z = 0} = Z := by
    ext z
    exact ⟨fun hz => ⟨hz.1, (haxis z (D.vertex_dual_subset_star v hv hz.1)).mpr
      ⟨interior_subset (hcore (D.inverse z).property), hz.2⟩⟩,
      fun hz => ⟨hz.1, ((haxis z (D.vertex_dual_subset_star v hv hz.1)).mp hz.2).2⟩⟩
  have hInter (eps delta : Bool) :
      sector eps delta ∩ sector eps (!delta) = face 1 eps ∧
      sector eps delta ∩ sector (!eps) delta = face 0 delta ∧
      sector eps delta ∩ sector (!eps) (!delta) = Z := by
    have h := signedCoordinateSector_incidence V.space coords (fun _ => true) eps delta
    rw [hSector, hSector, hSector, hSector, hFace, hFace, ← hAxisEq]
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hMeet (eps delta : Bool) : face 0 delta ∩ face 1 eps = Z := by
    rw [hFace, hFace, ← hAxisEq]
    exact (signedCoordinateSector_incidence V.space coords (fun _ => true) eps delta).2.2.2
  have hCover : (⋃ eps, ⋃ delta, sector eps delta) = V.space := by
    simp only [hSector]
    exact signedCoordinateSector_cover V.space coords (fun _ => true)
  choose maps hMaps hMapsFace hMapsEnd hMapsAxis hMapsBoundary using
    fun eps delta => hSectors ![eps, delta]
  have h0 (eps delta : Bool) (z : ↥(signedTubeRadius 0 delta ×ˢ Icc (0 : ℝ) 1)) :
      (maps eps delta ⟨z, (signedTube_quarter_ball eps delta).1
        (Or.inr (Or.inl z.property.1)), z.property.2⟩ : D.sample → ℝ × V3) =
          halfMap 0 delta z := hMapsFace eps delta 0 z
  have h1 (eps delta : Bool) (z : ↥(signedTubeRadius 1 eps ×ˢ Icc (0 : ℝ) 1)) :
      (maps eps delta ⟨z, (signedTube_quarter_ball eps delta).1
        (Or.inr (Or.inr z.property.1)), z.property.2⟩ : D.sample → ℝ × V3) =
          halfMap 1 eps z := hMapsFace eps delta 1 z
  obtain ⟨map, hmap, hkeep, hmem⟩ := exists_signed_sector_block_map 0 1 sector face Z V.space
    halfMap maps hMaps hInter hMeet hCover h0 h1
      (fun t => (axis t : D.sample → ℝ × V3)) hMapsAxis
  have hEnd (b : Bool) (z : signedTubeDiamond) :
      (map ⟨(z, if b then 1 else 0), z.property, by cases b <;> simp⟩ : D.sample → ℝ × V3) = G b z := by
    obtain ⟨eps, heps⟩ := mem_iUnion.mp z.property
    obtain ⟨delta, hz⟩ := mem_iUnion.mp heps
    exact (hkeep eps delta ⟨(z, if b then 1 else 0), hz, by cases b <;> simp⟩).trans
      (hMapsEnd eps delta b ⟨z, hz⟩)
  refine ⟨axis, map, hAxis, hmap, hEnd, ?_, hmem, ?_, ?_, ?_⟩
  · intro t
    exact (hkeep false false ⟨((0, 0), t), signedTube_center_mem, t.property⟩).trans
      (hMapsAxis false false t)
  · exact signed_prism_coordinate_sheet_preimage map coords hmem
  · intro z
    exact (signed_prism_coordinate_axis_preimage map coords hmem hAxisEq z).trans
      (and_iff_right (map z).property)
  · intro b z
    exact signed_prism_end_preimage (by cases b <;> simp) map (G b) (hEnd b) z

end PoincareConjecture.M76.Dehn.Annuli

