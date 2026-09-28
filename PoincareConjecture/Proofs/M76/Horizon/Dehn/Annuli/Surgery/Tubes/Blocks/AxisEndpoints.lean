import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalAxisEndpoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.IncidentQuarter

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_local_axis_parameter_of_ne
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hedges : s false ≠ s true) :
    let V := D.complex.barycentricDualBlock {v}
    let Z := V.space ∩ D.axis.space
    Z ∩ (V.link v).space = {(s false).centroid ℝ id, (s true).centroid ℝ id} ∧
      (s false).centroid ℝ id ≠ (s true).centroid ℝ id ∧
      IsFinitePLBallPair ℝ Z {(s false).centroid ℝ id, (s true).centroid ℝ id} ∧
      ∃ z : Icc (0 : ℝ) 1 ≃ₜ Z, z.IsFinitePL ∧
        (z ⟨0, le_rfl, zero_le_one⟩ : D.sample → ℝ × V3) = (s false).centroid ℝ id ∧
        (z ⟨1, zero_le_one, le_rfl⟩ : D.sample → ℝ × V3) = (s true).centroid ℝ id := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let Z := V.space ∩ D.axis.space
  let J := fun j ↦ (D.complex.barycentricDualBlock (s j)).space
  let center := fun j ↦ (s j).centroid ℝ id
  obtain ⟨x, y, C, hC, hface, haxis, _⟩ := D.exists_marked_raw_star v hv
  have hZ := (D.local_vertex_faces hcore v hv C hC hface haxis).1
  change IsFinitePLBallPair ℝ Z (Z ∩ (V.link v).space) at hZ
  have hJV (j : Bool) : J j ⊆ V.space :=
    space_subset_of_le (D.complex.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr (hvs j)))
  have hCenterJ (j : Bool) : center j ∈ J j :=
    (D.complex.barycentricDualBlock (s j)).vertices_subset_space
      (D.complex.faceCentroid_mem_barycentricDualBlock_vertices (D.axis_le (hs j)))
  have hCenterAxis (j : Bool) : center j ∈ D.axis.space := by
    let : Fintype D.axis.faces := (D.complex_finite.subset D.axis_le).fintype
    have hm := (D.axis.barycentricDualBlock (s j)).vertices_subset_space
      (D.axis.faceCentroid_mem_barycentricDualBlock_vertices (hs j))
    exact D.axis.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (D.axis.barycentricDualBlock_le (s j)) hm)
  have hCenterBoundary (j : Bool) : center j ∈ Z ∩ (V.link v).space :=
    ⟨⟨hJV j (hCenterJ j), hCenterAxis j⟩,
      D.joint_subset_vertex_link (s j) (hs j) (hcard j) v (hvs j) (hCenterJ j)⟩
  have hne : center false ≠ center true := by
    intro he
    exact hedges (congrArg Subtype.val (D.complex.faceCentroid_injective
      (a₁ := ⟨s false, D.axis_le (hs false)⟩) (a₂ := ⟨s true, D.axis_le (hs true)⟩) he))
  have hboundary : Z ∩ (V.link v).space = {center false, center true} := by
    obtain ⟨a, b, _, hp⟩ := hZ.exists_boundary_eq_pair
    have hm (j : Bool) : center j ∈ ({a, b} : Set (D.sample → ℝ × V3)) :=
      hp.subset (hCenterBoundary j)
    rw [hp]
    rcases hm false with h₀ | h₀ <;> rcases hm true with h₁ | h₁
    · exact False.elim (hne (h₀.trans h₁.symm))
    · simp only [h₀, show center true = b from h₁]
    · rw [h₀, show center true = a from h₁, pair_comm]
    · exact False.elim (hne (h₀.trans h₁.symm))
  rw [hboundary] at hZ
  exact ⟨hboundary, hne, hZ, hZ.exists_unitInterval_chart_with_endpoints hne⟩

open Classical in

theorem ComponentBranchModel.exists_local_axis_parameter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hdisj : Disjoint (D.complex.barycentricDualBlock (s false)).space
      (D.complex.barycentricDualBlock (s true)).space) :
    let V := D.complex.barycentricDualBlock {v}
    let Z := V.space ∩ D.axis.space
    Z ∩ (V.link v).space = {(s false).centroid ℝ id, (s true).centroid ℝ id} ∧
      (s false).centroid ℝ id ≠ (s true).centroid ℝ id ∧
      IsFinitePLBallPair ℝ Z {(s false).centroid ℝ id, (s true).centroid ℝ id} ∧
      ∃ z : Icc (0 : ℝ) 1 ≃ₜ Z, z.IsFinitePL ∧
        (z ⟨0, le_rfl, zero_le_one⟩ : D.sample → ℝ × V3) = (s false).centroid ℝ id ∧
        (z ⟨1, zero_le_one, le_rfl⟩ : D.sample → ℝ × V3) = (s true).centroid ℝ id := by
  apply D.exists_local_axis_parameter_of_ne hcore v hv s hs hcard hvs
  intro he
  have hc := (D.complex.barycentricDualBlock (s false)).vertices_subset_space
    (D.complex.faceCentroid_mem_barycentricDualBlock_vertices (D.axis_le (hs false)))
  exact disjoint_left.mp hdisj hc (he ▸ hc)

end PoincareConjecture.M76.Dehn.Annuli
