import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceDiskNormalLabels
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.IntrinsicDiskChartStars

/-!
# One constructed original-atlas proper-disk triangulation

The original graph, its inverse, all four full marked carriers and the
same labelled chart family are retained together. The graph ambient
dimension is unrestricted. No collar or cut is included in these data.
See Hudson1969, pp.12--19, 58--63 and rigidity018.
-/

set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]

open Classical in
/-- Actual outputs of the original proper-disk chart and graph
constructions, retained on one common finite model. Existence below
uses only the original proper disk. See rigidity018, sections1--3. -/
structure OriginalProperDiskTriangulation
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (j : V2 → X) where
  /-- The finite original graph index set. -/
  index : Finset R
  /-- The single original graph map. -/
  graph : X → (index → ℝ × V3)
  /-- The compact original neighborhood being modeled. -/
  neighborhood : Set X
  /-- The common finite geometric complex. -/
  ambient : SimplicialComplex ℝ (index → ℝ × V3)
  /-- Region, old frontier, disk and entire rim, in that order. -/
  marked : Fin 4 → SimplicialComplex ℝ (index → ℝ × V3)
  /-- The actual homeomorphism represented by the same graph. -/
  model : neighborhood ≃ₜ ambient.space
  /-- A total representative of the literal model inverse. -/
  inverse : (index → ℝ × V3) → neighborhood
  /-- The retained original square parameter. -/
  parameter : (index → ℝ × V3) → V2
  /-- Compactness of the whole original neighborhood. -/
  compact_neighborhood : IsCompact neighborhood
  /-- The whole region lies in the original ambient interior. -/
  region_interior : R ⊆ interior neighborhood
  /-- The same graph map is continuous on X. -/
  graph_continuous : Continuous graph
  /-- The graph has actual finite local formulas in every old chart. -/
  graph_originalPL : ∀ i,
    LocallyPiecewiseAffineOn (graph ∘ (e i).symm) (e i).target
  /-- Finiteness of the common complex. -/
  finite : ambient.faces.Finite
  /-- Every mark is an actual subcomplex of the same ambient complex. -/
  marked_le : ∀ i, marked i ≤ ambient
  /-- Each whole mark is full. -/
  marked_full : ∀ i t, t ∈ ambient.faces →
    (∀ v ∈ t, v ∈ (marked i).vertices) → t ∈ (marked i).faces
  /-- The entire modeled neighborhood image. -/
  ambient_space : ambient.space = graph '' neighborhood
  /-- The complete original region image. -/
  region_space : (marked 0).space = graph '' R
  /-- The complete original frontier image. -/
  boundary_space : (marked 1).space = graph '' frontier R
  /-- The entire original disk image. -/
  disk_space : (marked 2).space = graph '' (j '' D)
  /-- The entire original rim image. -/
  rim_space : (marked 3).space = graph '' (j '' Q)
  /-- Exact original disk contact with the whole old frontier. -/
  disk_boundary_inter : (marked 2).space ∩ (marked 1).space = (marked 3).space
  /-- The model is the literal graph on the entire neighborhood. -/
  model_eq : ∀ x : neighborhood, (model x : index → ℝ × V3) = graph x
  /-- Continuity of the actual inverse on the complete carrier. -/
  inverse_continuous : ContinuousOn inverse ambient.space
  /-- The total inverse retains the actual homeomorphism inverse. -/
  inverse_eq : ∀ x : ambient.space, (inverse x : X) = (model.symm x : X)
  /-- Original-atlas PL certificates for that same inverse. -/
  inverse_originalPL :
    PolyhedralPLInCharts e (fun x => (inverse x : X)) ambient.space
  /-- The original parameter is affine on every common face. -/
  parameter_affine : ambient.AffineOnFaces parameter
  /-- Every original square parameter value is retained. -/
  parameter_original : ∀ z : D, parameter (graph (j z)) = (z : V2)
  /-- The original local affine chart projections are unchanged. -/
  projections : ∀ x ∈ neighborhood,
    ∃ (i : ι) (V : Set X) (a : (index → ℝ × V3) →ᴬ[ℝ] V3),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ graph) (e i) V
  /-- The whole actual disk remains in the original region. -/
  disk_in_region : MapsTo j D R
  /-- The single restricted original PL pair-chart family. -/
  chart : D → OpenPartialHomeomorph X C3
  /-- One constant normal label for each entire original chart. -/
  weight : D → ℝ
  /-- Each original parameter point lies in its selected chart. -/
  chart_point : ∀ z : D, j z ∈ (chart z).source
  /-- The original chart center is retained. -/
  chart_center : ∀ z : D, chart z (j z) = 0
  /-- Both whole original-atlas transition directions are PL. -/
  chart_compatible : ∀ z i,
    LocallyPiecewiseAffineOn ((e i).symm.trans (chart z))
      ((e i).symm.trans (chart z)).source ∧
    LocallyPiecewiseAffineOn ((chart z).symm.trans (e i))
      ((chart z).symm.trans (e i)).source
  /-- The complete original region/disk pair on each chart source. -/
  chart_model : ∀ z,
    ((chart z).source ⊆ interior R ∧
      ∀ x ∈ (chart z).source, x ∈ j '' D ↔ (chart z x).2 = 0) ∨
    ((∀ x ∈ (chart z).source, x ∈ R ↔ 0 ≤ (chart z x).1.1) ∧
      ∀ x ∈ (chart z).source, x ∈ j '' D ↔ 0 ≤ (chart z x).1.1 ∧ (chart z x).2 = 0)
  /-- Each label preserves both strict sides. -/
  weight_nonzero : ∀ z, weight z ≠ 0
  /-- Literal sign agreement on an actual relative original overlap. -/
  overlap : ∀ i k (z : D), j z ∈ (chart i).source ∩ (chart k).source →
    ∃ V : Set R, IsOpen V ∧ (⟨j z, disk_in_region z.property⟩ : R) ∈ V ∧
      MapsTo (Subtype.val : R → X) V ((chart i).source ∩ (chart k).source) ∧
      EqOn (fun y : R => sign (weight i * (chart i (y : X)).2))
        (fun y : R => sign (weight k * (chart k (y : X)).2)) V
  /-- One index from that same family for each actual disk vertex. -/
  chart_index : (marked 2).vertices → D
  /-- The selected source contains the whole transported star. -/
  star_source : ∀ p : (marked 2).vertices,
    MapsTo (fun x => (inverse x : X)) (ambient.closedStar p).space
      (chart (chart_index p)).source
  /-- The literal selected chart is affine on every whole star face. -/
  star_affine : ∀ p : (marked 2).vertices,
    (ambient.closedStar p).AffineOnFaces (fun x => chart (chart_index p) (inverse x))
  /-- Injectivity on the whole star, in the genuine chart model. -/
  star_injective : ∀ p : (marked 2).vertices,
    InjOn (fun x => chart (chart_index p) (inverse x)) (ambient.closedStar p).space
  /-- A genuine original open neighborhood inside each transported star. -/
  star_neighborhood : ∀ p : (marked 2).vertices,
    ∃ O : Set X, IsOpen O ∧ (inverse p : X) ∈ O ∧
      O ⊆ (chart (chart_index p)).source ∧
      O ⊆ (fun x => (inverse x : X)) '' (ambient.closedStar p).space
  /-- Interior is in the original three-dimensional chart target. -/
  star_interior : ∀ p : (marked 2).vertices,
    chart (chart_index p) (inverse p) ∈
      interior ((fun x => chart (chart_index p) (inverse x)) '' (ambient.closedStar p).space)

/-- The original compact PL domain and actual proper disk construct
the complete record with a single fixed labelled chart family.
No block, collar or cut premise is added. See rigidity018, section3. -/
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

end PoincareMT.M76
