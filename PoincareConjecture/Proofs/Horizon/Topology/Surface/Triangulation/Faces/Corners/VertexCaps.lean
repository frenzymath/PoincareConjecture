


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Sectors.Intersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.SectorCaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CapTransversality









set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M}



structure VertexCapFaces (P : ChartCircleArrangementVertexPatch r p)
    (x : Bool × Bool → M) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_width : scale < P.width
  planarCoordinates : Bool × Bool →
    OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2))
  coordinates : Bool × Bool → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M
  face : Bool × Bool → SmoothFace M
  planar_source : ∀ i, {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ scale} ⊆
    (planarCoordinates i).source
  planar_target : ∀ i, (planarCoordinates i).target ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).target
  planar_smooth : ∀ i, ContDiffOn ℝ ∞ (planarCoordinates i) (planarCoordinates i).source
  planar_smooth_symm : ∀ i, ContDiffOn ℝ ∞ (planarCoordinates i).symm (planarCoordinates i).target
  planar_first : ∀ i s, s ∈ Icc (0 : ℝ) scale → planarCoordinates i (s, 0) =
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (s, 0))
  planar_second : ∀ i t, t ∈ Icc (0 : ℝ) scale → planarCoordinates i (0, t) =
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, t))
  planar_chord : ∀ i t, planarCoordinates i ((1 - t) * scale, t * scale) =
    (1 - t) • planarCoordinates i (scale, 0) + t • planarCoordinates i (0, scale)
  coordinates_apply : ∀ i z, coordinates i z =
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).symm (planarCoordinates i (collarParameterEquiv z))
  triangle_subset_source : ∀ i, convexHull ℝ (range (rightTriangleBasis scale_pos)) ⊆
    (coordinates i).source
  coordinates_target : ∀ i, (coordinates i).target ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source
  coordinates_smooth : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates i) (coordinates i).source
  coordinates_smooth_symm : ∀ i,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (coordinates i).symm (coordinates i).target
  face_map : ∀ i, (face i).map = coordinates i
  face_source : ∀ i, (face i).source = convexHull ℝ (range (rightTriangleBasis scale_pos))
  carrier_eq : ∀ i, (face i).carrier =
    coordinates i '' convexHull ℝ (range (rightTriangleBasis scale_pos))
  carrier_planar : ∀ i, (face i).carrier =
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).symm ''
      (planarCoordinates i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ scale})
  face_injective : ∀ i, InjOn (face i).map (face i).source
  boundary_map : ∀ i (k : Fin 3), ((face i).boundary k).map = coordinates i ∘
    affineChartSegment (rightTriangleBasis scale_pos (k.succAbove 0))
      (rightTriangleBasis scale_pos (k.succAbove 1))
  boundary_injective : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1)
  chord_map : ∀ i t, ((face i).boundary 0).map t =
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).symm
      ((1 - t) • chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (scale, 0)) +
        t • chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, scale)))
  second_map : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ((face i).boundary 1).map t = P.sectorCoordinates i (0, t * scale)
  first_map : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ((face i).boundary 2).map t = P.sectorCoordinates i (t * scale, 0)
  chord_image : ∀ i, ((face i).boundary 0).map '' Icc (0 : ℝ) 1 =
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).symm '' affineSegment ℝ
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (scale, 0)))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, scale)))
  second_image : ∀ i, ((face i).boundary 1).map '' Icc (0 : ℝ) 1 = P.secondSide i scale
  first_image : ∀ i, ((face i).boundary 2).map '' Icc (0 : ℝ) 1 = P.firstSide i scale
  carrier_subset_sector : ∀ i, (face i).carrier ⊆ P.closedSector i
  carrier_subset_sector_sides : ∀ i, (face i).carrier ⊆
    P.sector i ∪ (P.firstSide i scale ∪ P.secondSide i scale)
  neighborhood : Set M
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : p ∈ neighborhood
  neighborhood_subset_carriers : neighborhood ⊆ ⋃ i, (face i).carrier



theorem exists_vertexCapFaces_at_scale (P : ChartCircleArrangementVertexPatch r p)
    (x : Bool × Bool → M)
    (hchart : ∀ i, P.closedSector i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source) :
    ∃ ρ > 0, ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ B : VertexCapFaces P x, B.scale = ε := by
  classical
  choose δ hδ hδwidth hcaps using fun i => P.exists_smoothFace_sector_caps i (x i) (hchart i)
  let μ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hμ : 0 < μ := by simpa [μ] using hδ
  have hμle (i : Bool × Bool) : μ ≤ δ i := Finset.inf'_le δ (Finset.mem_univ i)
  refine ⟨μ, hμ, ?_⟩
  intro ε hε hεμ
  have hεδ (i : Bool × Bool) : ε < δ i := hεμ.trans_le (hμle i)
  have hεwidth : ε < P.width := (hεδ (false, false)).trans_le (hδwidth (false, false))
  choose F C face hFsource hFtarget hF hFI hplanar_first hplanar_second hplanar_chord
    hCmap hsource hCtarget hC hCI hmap hface_source
    hcarrier hcarrier_planar hinj hboundary hedgeinj hchord hsecond hfirst
    hchord_image hsecond_image hfirst_image hsector hsides V hVopen hVp hVcover using
      fun i => hcaps i ε hε (hεδ i)
  obtain ⟨U, hUopen, hUp, hUcover⟩ := P.exists_neighborhood_subset_sector_caps
    (fun i => (face i).carrier) (fun i => ⟨V i, hVopen i, hVp i, hVcover i⟩)
  exact ⟨{
    scale := ε
    scale_pos := hε
    scale_lt_width := hεwidth
    planarCoordinates := F
    coordinates := C
    face := face
    planar_source := hFsource
    planar_target := hFtarget
    planar_smooth := hF
    planar_smooth_symm := hFI
    planar_first := hplanar_first
    planar_second := hplanar_second
    planar_chord := hplanar_chord
    coordinates_apply := hCmap
    triangle_subset_source := hsource
    coordinates_target := hCtarget
    coordinates_smooth := hC
    coordinates_smooth_symm := hCI
    face_map := hmap
    face_source := hface_source
    carrier_eq := hcarrier
    carrier_planar := hcarrier_planar
    face_injective := hinj
    boundary_map := hboundary
    boundary_injective := hedgeinj
    chord_map := hchord
    second_map := hsecond
    first_map := hfirst
    chord_image := hchord_image
    second_image := fun i => by
      simpa only [singleton_prod, image_image, secondSide, Function.comp_def] using hsecond_image i
    first_image := fun i => by
      simpa only [prod_singleton, image_image, firstSide, Function.comp_def] using hfirst_image i
    carrier_subset_sector := hsector
    carrier_subset_sector_sides := fun i => by
      simpa only [image_union, prod_singleton, singleton_prod, image_image, firstSide, secondSide,
        Function.comp_def] using hsides i
    neighborhood := U
    isOpen_neighborhood := hUopen
    mem_neighborhood := hUp
    neighborhood_subset_carriers := hUcover }, rfl⟩



theorem exists_vertexCapFaces (P : ChartCircleArrangementVertexPatch r p)
    (x : Bool × Bool → M)
    (hchart : ∀ i, P.closedSector i ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source) :
    Nonempty (VertexCapFaces P x) := by
  obtain ⟨ρ, hρ, hcaps⟩ := P.exists_vertexCapFaces_at_scale x hchart
  obtain ⟨B, _⟩ := hcaps (ρ / 2) (half_pos hρ) (half_lt_self hρ)
  exact ⟨B⟩

namespace VertexCapFaces

variable {P : ChartCircleArrangementVertexPatch r p} {x : Bool × Bool → M}
  (B : VertexCapFaces P x)

theorem firstSide_subset_carrier (i : Bool × Bool) : P.firstSide i B.scale ⊆ (B.face i).carrier := by
  rw [← B.first_image i]
  exact ((B.face i).boundary_image_subset_frontier 2).trans (B.face i).isClosed_carrier.frontier_subset

theorem secondSide_subset_carrier (i : Bool × Bool) : P.secondSide i B.scale ⊆ (B.face i).carrier := by
  rw [← B.second_image i]
  exact ((B.face i).boundary_image_subset_frontier 1).trans (B.face i).isClosed_carrier.frontier_subset

theorem mem_carrier (i : Bool × Bool) : p ∈ (B.face i).carrier :=
  B.firstSide_subset_carrier i (P.mem_firstSide i B.scale_pos.le)

omit [T2Space M] in
theorem carrier_subset_patch (i : Bool × Bool) : (B.face i).carrier ⊆ P.carrier :=
  (B.carrier_subset_sector i).trans (P.closedSector_subset_carrier i)

omit [T2Space M] in
theorem carrier_subset_chart (i : Bool × Bool) : (B.face i).carrier ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source := by
  rw [B.carrier_eq i]
  rintro _ ⟨z, hz, rfl⟩
  exact B.coordinates_target i ((B.coordinates i).map_source (B.triangle_subset_source i hz))

omit [T2Space M] in


theorem first_boundary_agreement {i j : Bool × Bool} (hij : i.1 = j.1) :
    EqOn ((B.face i).boundary 2).map ((B.face j).boundary 2).map (Icc (0 : ℝ) 1) := by
  intro t ht
  rw [B.first_map i t ht, B.first_map j t ht]
  change P.productCoordinates (sectorParameterEquiv P.center i (t * B.scale, 0)) =
    P.productCoordinates (sectorParameterEquiv P.center j (t * B.scale, 0))
  simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]

omit [T2Space M] in


theorem second_boundary_agreement {i j : Bool × Bool} (hij : i.2 = j.2) :
    EqOn ((B.face i).boundary 1).map ((B.face j).boundary 1).map (Icc (0 : ℝ) 1) := by
  intro t ht
  rw [B.second_map i t ht, B.second_map j t ht]
  change P.productCoordinates (sectorParameterEquiv P.center i (0, t * B.scale)) =
    P.productCoordinates (sectorParameterEquiv P.center j (0, t * B.scale))
  simp only [sectorParameterEquiv_apply, hij, neg_zero, ite_self]



theorem intersections {i j : Bool × Bool} (hij : i ≠ j) :
    (i.1 = j.1 → (B.face i).carrier ∩ (B.face j).carrier = P.firstSide i B.scale) ∧
    (i.2 = j.2 → (B.face i).carrier ∩ (B.face j).carrier = P.secondSide i B.scale) ∧
    (i.1 ≠ j.1 → i.2 ≠ j.2 → (B.face i).carrier ∩ (B.face j).carrier = {p}) :=
  P.cap_intersections B.scale_pos.le B.scale_lt_width.le (fun i => (B.face i).carrier)
    B.carrier_subset_sector B.carrier_subset_sector_sides B.firstSide_subset_carrier
    B.secondSide_subset_carrier hij



theorem intersection_edge_or_vertex {i j : Bool × Bool} (hij : i ≠ j) :
    (∃ k : Fin 3, (B.face i).carrier ∩ (B.face j).carrier =
        ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((B.face j).boundary k).map '' Icc (0 : ℝ) 1) ∨
      (B.face i).carrier ∩ (B.face j).carrier = {p} := by
  by_cases hfst : i.1 = j.1
  · left
    refine ⟨2, ?_, ?_⟩
    · rw [B.first_image]
      exact (B.intersections hij).1 hfst
    · rw [B.first_image, B.first_image]
      exact P.firstSide_eq_of_fst_eq hfst B.scale
  by_cases hsnd : i.2 = j.2
  · left
    refine ⟨1, ?_, ?_⟩
    · rw [B.second_image]
      exact (B.intersections hij).2.1 hsnd
    · rw [B.second_image, B.second_image]
      exact P.secondSide_eq_of_snd_eq hsnd B.scale
  exact Or.inr ((B.intersections hij).2.2 hfst hsnd)




theorem endpoint_transversality (i : Bool × Bool) :
    let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun s => chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (s, 0))
    let g : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t => chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, t))
    LinearIndependent ℝ (![deriv f B.scale, g B.scale - f B.scale] : Fin 2 → EuclideanSpace ℝ (Fin 2)) ∧
    LinearIndependent ℝ (![deriv g B.scale, f B.scale - g B.scale] : Fin 2 → EuclideanSpace ℝ (Fin 2)) ∧
    fderiv ℝ (capExcess (B.planarCoordinates i) B.scale) (f B.scale) (deriv f B.scale) = 1 ∧
    fderiv ℝ (capExcess (B.planarCoordinates i) B.scale) (g B.scale) (deriv g B.scale) = 1 := by
  let H := P.chartSectorCoordinates (x i) i
  have hsquare₁ : (B.scale, (0 : ℝ)) ∈ Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width :=
    ⟨⟨B.scale_pos.le, B.scale_lt_width.le⟩, ⟨le_rfl, P.width_pos.le⟩⟩
  have hsquare₂ : ((0 : ℝ), B.scale) ∈ Icc (0 : ℝ) P.width ×ˢ Icc (0 : ℝ) P.width :=
    ⟨⟨le_rfl, P.width_pos.le⟩, ⟨B.scale_pos.le, B.scale_lt_width.le⟩⟩
  have hq₁ : (B.scale, (0 : ℝ)) ∈ H.source :=
    ⟨P.sectorCoordinates_square_source i hsquare₁,
      B.carrier_subset_chart i (B.firstSide_subset_carrier i ⟨B.scale, ⟨B.scale_pos.le, le_rfl⟩, rfl⟩)⟩
  have hq₂ : ((0 : ℝ), B.scale) ∈ H.source :=
    ⟨P.sectorCoordinates_square_source i hsquare₂,
      B.carrier_subset_chart i (B.secondSide_subset_carrier i ⟨B.scale, ⟨B.scale_pos.le, le_rfl⟩, rfl⟩)⟩
  have hdH₁ := ((P.chartSectorCoordinates_smooth (x i) i _ hq₁).contDiffAt
    (H.open_source.mem_nhds hq₁)).differentiableAt (by simp) |>.hasFDerivAt
  have hdH₂ := ((P.chartSectorCoordinates_smooth (x i) i _ hq₂).contDiffAt
    (H.open_source.mem_nhds hq₂)).differentiableAt (by simp) |>.hasFDerivAt
  apply cap_endpoint_transversality_of_axis_maps (B.planarCoordinates i)
    (B.planar_smooth i) (B.planar_smooth_symm i) B.scale_pos (B.planar_source i)
    (fun t _ => B.planar_chord i t) ?_ ?_ (B.planar_first i) (B.planar_second i)
  · exact (hdH₁.comp_hasDerivAt (f := fun s : ℝ => (s, 0)) B.scale
      ((hasDerivAt_id B.scale).prodMk (hasDerivAt_const B.scale (0 : ℝ)))).differentiableAt
  · exact (hdH₂.comp_hasDerivAt (f := fun t : ℝ => (0, t)) B.scale
      ((hasDerivAt_const B.scale (0 : ℝ)).prodMk (hasDerivAt_id B.scale))).differentiableAt

omit [T2Space M] in


theorem capExcess_nonpos_on_carrier (i : Bool × Bool) :
    ∀ z ∈ (B.face i).carrier, capExcess (B.planarCoordinates i) B.scale
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) z) ≤ 0 := by
  intro z hz
  rw [B.carrier_planar i] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have htarget : w ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).target := by
    obtain ⟨q, hq, rfl⟩ := hw
    exact B.planar_target i ((B.planarCoordinates i).map_source (B.planar_source i hq))
  rw [(chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).right_inv htarget]
  exact capExcess_nonpos_on_cap (B.planarCoordinates i) (B.planar_source i) w hw

end VertexCapFaces
end ChartCircleArrangementVertexPatch
end PoincareConjecture.Topology.Surface
