import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskNormalLabels
import PoincareConjecture.Proofs.M76.Rigidity.IntrinsicDiskChartStars

set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]

open Classical in

structure OriginalProperDiskTriangulation
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (j : V2 → X) where

  index : Finset R

  graph : X → (index → ℝ × V3)

  neighborhood : Set X

  ambient : SimplicialComplex ℝ (index → ℝ × V3)

  marked : Fin 4 → SimplicialComplex ℝ (index → ℝ × V3)

  model : neighborhood ≃ₜ ambient.space

  inverse : (index → ℝ × V3) → neighborhood

  parameter : (index → ℝ × V3) → V2

  compact_neighborhood : IsCompact neighborhood

  region_interior : R ⊆ interior neighborhood

  graph_continuous : Continuous graph

  graph_originalPL : ∀ i,
    LocallyPiecewiseAffineOn (graph ∘ (e i).symm) (e i).target

  finite : ambient.faces.Finite

  marked_le : ∀ i, marked i ≤ ambient

  marked_full : ∀ i t, t ∈ ambient.faces →
    (∀ v ∈ t, v ∈ (marked i).vertices) → t ∈ (marked i).faces

  ambient_space : ambient.space = graph '' neighborhood

  region_space : (marked 0).space = graph '' R

  boundary_space : (marked 1).space = graph '' frontier R

  disk_space : (marked 2).space = graph '' (j '' D)

  rim_space : (marked 3).space = graph '' (j '' Q)

  disk_boundary_inter : (marked 2).space ∩ (marked 1).space = (marked 3).space

  model_eq : ∀ x : neighborhood, (model x : index → ℝ × V3) = graph x

  inverse_continuous : ContinuousOn inverse ambient.space

  inverse_eq : ∀ x : ambient.space, (inverse x : X) = (model.symm x : X)

  inverse_originalPL :
    PolyhedralPLInCharts e (fun x => (inverse x : X)) ambient.space

  parameter_affine : ambient.AffineOnFaces parameter

  parameter_original : ∀ z : D, parameter (graph (j z)) = (z : V2)

  projections : ∀ x ∈ neighborhood,
    ∃ (i : ι) (V : Set X) (a : (index → ℝ × V3) →ᴬ[ℝ] V3),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ graph) (e i) V

  disk_in_region : MapsTo j D R

  chart : D → OpenPartialHomeomorph X C3

  weight : D → ℝ

  chart_point : ∀ z : D, j z ∈ (chart z).source

  chart_center : ∀ z : D, chart z (j z) = 0

  chart_compatible : ∀ z i,
    LocallyPiecewiseAffineOn ((e i).symm.trans (chart z))
      ((e i).symm.trans (chart z)).source ∧
    LocallyPiecewiseAffineOn ((chart z).symm.trans (e i))
      ((chart z).symm.trans (e i)).source

  chart_model : ∀ z,
    ((chart z).source ⊆ interior R ∧
      ∀ x ∈ (chart z).source, x ∈ j '' D ↔ (chart z x).2 = 0) ∨
    ((∀ x ∈ (chart z).source, x ∈ R ↔ 0 ≤ (chart z x).1.1) ∧
      ∀ x ∈ (chart z).source, x ∈ j '' D ↔ 0 ≤ (chart z x).1.1 ∧ (chart z x).2 = 0)

  weight_nonzero : ∀ z, weight z ≠ 0

  overlap : ∀ i k (z : D), j z ∈ (chart i).source ∩ (chart k).source →
    ∃ V : Set R, IsOpen V ∧ (⟨j z, disk_in_region z.property⟩ : R) ∈ V ∧
      MapsTo (Subtype.val : R → X) V ((chart i).source ∩ (chart k).source) ∧
      EqOn (fun y : R => sign (weight i * (chart i (y : X)).2))
        (fun y : R => sign (weight k * (chart k (y : X)).2)) V

  chart_index : (marked 2).vertices → D

  star_source : ∀ p : (marked 2).vertices,
    MapsTo (fun x => (inverse x : X)) (ambient.closedStar p).space
      (chart (chart_index p)).source

  star_affine : ∀ p : (marked 2).vertices,
    (ambient.closedStar p).AffineOnFaces (fun x => chart (chart_index p) (inverse x))

  star_injective : ∀ p : (marked 2).vertices,
    InjOn (fun x => chart (chart_index p) (inverse x)) (ambient.closedStar p).space

  star_neighborhood : ∀ p : (marked 2).vertices,
    ∃ O : Set X, IsOpen O ∧ (inverse p : X) ∈ O ∧
      O ⊆ (chart (chart_index p)).source ∧
      O ⊆ (fun x => (inverse x : X)) '' (ambient.closedStar p).space

  star_interior : ∀ p : (marked 2).vertices,
    chart (chart_index p) (inverse p) ∈
      interior ((fun x => chart (chart_index p) (inverse x)) '' (ambient.closedStar p).space)

theorem exists_original_proper_disk_triangulation [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) :
    Nonempty (OriginalProperDiskTriangulation e R j) := by
  classical
  obtain ⟨B, w, hB, hoverlap⟩ :=
    exists_original_proper_disk_normal_labels he hj hemb hDR hproper
  obtain ⟨s, F, C, K, A, H, g, u, hC, hRC, hFc, hFPL, hK, hA,
    hKs, hA0, hA1, hA2, hA3, hAint, hHF, hgc, hg, hgPL, huf, hu, hproj, hstars⟩ :=
    exists_intrinsic_proper_disk_chart_stars hR he hj hemb hDR hproper B
      (fun z => (hB z).1) (fun z i => ((hB z).2.2.1 i).1)
  choose z hsource hface hinj hneighborhood hinterior using
    fun p : (A 2).vertices => hstars p p.property
  exact ⟨{
    index := s
    graph := F
    neighborhood := C
    ambient := K
    marked := A
    model := H
    inverse := g
    parameter := u
    compact_neighborhood := hC
    region_interior := hRC
    graph_continuous := hFc
    graph_originalPL := hFPL
    finite := hK
    marked_le := fun i => (hA i).1
    marked_full := fun i => (hA i).2.2
    ambient_space := hKs
    region_space := hA0
    boundary_space := hA1
    disk_space := hA2
    rim_space := hA3
    disk_boundary_inter := hAint
    model_eq := hHF
    inverse_continuous := hgc
    inverse_eq := hg
    inverse_originalPL := hgPL
    parameter_affine := huf
    parameter_original := hu
    projections := hproj
    disk_in_region := hDR
    chart := B
    weight := w
    chart_point := fun z => (hB z).1
    chart_center := fun z => (hB z).2.1
    chart_compatible := fun z => (hB z).2.2.1
    chart_model := fun z => (hB z).2.2.2.1
    weight_nonzero := fun z => (hB z).2.2.2.2
    overlap := hoverlap
    chart_index := z
    star_source := hsource
    star_affine := hface
    star_injective := hinj
    star_neighborhood := hneighborhood
    star_interior := hinterior }⟩

end PoincareConjecture.M76
