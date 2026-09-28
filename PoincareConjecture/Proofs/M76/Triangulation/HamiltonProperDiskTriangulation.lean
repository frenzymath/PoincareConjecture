import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFullChartStars
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralFrontierRegion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




structure HamiltonProperDiskPairChart (R D : Set E) where

  chart : OpenPartialHomeomorph E V

  piecewiseAffine : LocallyPiecewiseAffineOn chart chart.source

  inverse_piecewiseAffine : LocallyPiecewiseAffineOn chart.symm chart.target

  model :
    (chart.source ⊆ interior R ∧
      ∀ x ∈ chart.source, x ∈ D ↔ (chart x).2 = 0) ∨
    ((∀ x ∈ chart.source, x ∈ R ↔ 0 ≤ (chart x).1.1) ∧
      ∀ x ∈ chart.source, x ∈ D ↔ 0 ≤ (chart x).1.1 ∧ (chart x).2 = 0)

variable [DecidableEq E]





structure HamiltonProperDiskTriangulation (R D : Set E)
    (b : closedBall (0 : V2) 1 ≃ₜ D) where

  ambient : SimplicialComplex ℝ E

  region : SimplicialComplex ℝ E

  disk : SimplicialComplex ℝ E

  boundary : SimplicialComplex ℝ E

  finite : ambient.faces.Finite

  region_le : region ≤ ambient

  disk_le : disk ≤ ambient

  boundary_le : boundary ≤ ambient

  region_space : region.space = R

  disk_space : disk.space = D

  boundary_space : boundary.space = frontier R

  region_interior : R ⊆ interior ambient.space

  disk_full : ∀ s ∈ ambient.faces,
    (∀ v ∈ s, v ∈ disk.vertices) → s ∈ disk.faces

  inverse : E → V2

  inverse_affine : disk.AffineOnFaces inverse

  inverse_eq : ∀ x : D, inverse x = b.symm x

  pairChart : disk.vertices → HamiltonProperDiskPairChart R D

  star_source : ∀ p : disk.vertices,
    (ambient.closedStar p).space ⊆ (pairChart p).chart.source

  star_affine : ∀ p : disk.vertices,
    (ambient.closedStar p).AffineOnFaces (pairChart p).chart






theorem exists_proper_disk_triangulation_of_pair_charts
    {R D : Set E} (hR : IsCompact R) (hreg : closure (interior R) = R)
    (hDR : D ⊆ R) (b : closedBall (0 : V2) 1 ≃ₜ D) (hb : b.IsFinitePL)
    (JF : SimplicialComplex ℝ E) (hJF : JF.faces.Finite)
    (hfront : JF.space = frontier R)
    (hcharts : ∀ p : D, ∃ H : HamiltonProperDiskPairChart R D,
      (p : E) ∈ H.chart.source) :
    Nonempty (HamiltonProperDiskTriangulation R D b) := by
  classical
  obtain ⟨JR, _, hJR, _, hJRspace, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_of_polyhedral_frontier hR hreg
      JF hJF hfront
  obtain ⟨u, hu, hbu⟩ := hb.symm
  have hucopy := hu
  obtain ⟨JD, hJD, hJDspace, _⟩ := hucopy
  obtain ⟨K0, hK0, hRK0, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hR isOpen_univ (subset_univ R)
  obtain ⟨g, hg, hgu, _, _⟩ := hu.exists_supported_extension K0 hK0
    (hDR.trans (hRK0.trans interior_subset)) isOpen_univ (subset_univ D)
  obtain ⟨T, hT, hTK0, hgT⟩ := hg
  obtain ⟨K, hK, hKK0, hKT⟩ := K0.exists_common_finite_subdivision T hK0 hT hTK0.symm
  have hgK : K.AffineOnFaces g := hKT.affineOnFaces hgT
  have hRK : R ⊆ interior K.space := by rwa [hKK0.space_eq]
  let J : Fin 3 → SimplicialComplex ℝ E := ![JR, JD, JF]
  have hJ (i : Fin 3) : (J i).faces.Finite := by
    fin_cases i
    · exact hJR
    · exact hJD
    · exact hJF
  have hJK (i : Fin 3) : (J i).space ⊆ K.space := by
    fin_cases i
    · change JR.space ⊆ K.space
      rw [hJRspace]
      exact hRK.trans interior_subset
    · change JD.space ⊆ K.space
      rw [hJDspace]
      exact hDR.trans (hRK.trans interior_subset)
    · change JF.space ⊆ K.space
      rw [hfront]
      exact hR.isClosed.frontier_subset.trans (hRK.trans interior_subset)
  choose H hpH using hcharts
  obtain ⟨S, L, hS, hSK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_local_chart_stars hK J hJ hJK hu.isCompact
      (hDR.trans hRK) (fun p => (H p).chart) (fun p => (H p).chart.source)
      (fun p => (H p).piecewiseAffine) hpH
  have hLD : (L 1).space = D := (hL 1).2.1.trans hJDspace
  have hselect (p : (L 1).vertices) : ∃ q : D,
      (S.closedStar p).space ⊆ (H q).chart.source ∧
      (S.closedStar p).AffineOnFaces (H q).chart := by
    have hpS : (p : E) ∈ S.vertices := (hL 1).1 p.property
    have hpD : (p : E) ∈ D := hLD.subset ((L 1).vertices_subset_space p.property)
    exact hstars p hpS hpD
  choose q hsource haffine using hselect
  refine ⟨{
    ambient := S
    region := L 0
    disk := L 1
    boundary := L 2
    finite := hS
    region_le := (hL 0).1
    disk_le := (hL 1).1
    boundary_le := (hL 2).1
    region_space := (hL 0).2.1.trans hJRspace
    disk_space := hLD
    boundary_space := (hL 2).2.1.trans hfront
    region_interior := ?_
    disk_full := (hL 1).2.2
    inverse := g
    inverse_affine := fun s hs => (hSK.affineOnFaces hgK) s ((hL 1).1 hs)
    inverse_eq := fun x => (hgu x.property).trans (hbu x).symm
    pairChart := fun p => H (q p)
    star_source := hsource
    star_affine := haffine }⟩
  rwa [hSK.space_eq]

end PoincareConjecture.M76.HamiltonIndexOne
