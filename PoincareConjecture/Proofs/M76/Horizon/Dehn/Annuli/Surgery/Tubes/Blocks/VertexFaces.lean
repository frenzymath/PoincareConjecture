import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalVertexFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Joints.IncidentJoints

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.vertex_mem_interior_core
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    (D.inverse p : X) ∈ interior D.core := by
  apply D.core_neighborhood
  obtain ⟨a, ha, hap⟩ := D.axis_space.subset (D.axis.vertices_subset_space hp)
  refine ⟨a, ha, ?_⟩
  exact (D.graph_separates _ (D.inverse p).property _
    ((D.graph_inverse p (D.complex.vertices_subset_space (D.axis_le hp))).trans hap.symm)).symm

theorem ComponentBranchModel.vertex_dual_subset_star
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    (D.complex.barycentricDualBlock {p}).space ⊆ (D.complex.closedStar p).space := by
  intro z hz
  obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
  obtain ⟨t, ht, hst⟩ := D.complex.exists_original_star_face_of_vertex_dual_face (D.axis_le hp) hs
  exact (D.complex.closedStar p).convexHull_subset_space ht (hst hzs)

open Classical in
set_option maxHeartbeats 800000 in

theorem ComponentBranchModel.local_vertex_faces
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices)
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source)
    (hface : (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar p).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) :
    let V := D.complex.barycentricDualBlock {p}
    let Z := V.space ∩ D.axis.space
    let bZ := Z ∩ (V.link p).space
    IsFinitePLBallPair ℝ Z bZ ∧
      ∀ (j : Fin 2) (b : Bool),
        let F := {z | z ∈ V.space ∧ C.chart (D.inverse z) j.castSucc = 0 ∧
          if b then 0 ≤ C.chart (D.inverse z) j.rev.castSucc
          else C.chart (D.inverse z) j.rev.castSucc ≤ 0}
        let O := F ∩ (V.link p).space
        IsFinitePLBallPair P2 F (Z ∪ O) ∧ IsFinitePLBallPair ℝ O bZ := by
  classical
  let V := D.complex.barycentricDualBlock {p}
  have hpstar : p ∈ (D.complex.closedStar p).space := by
    apply (D.complex.closedStar p).vertices_subset_space
    exact ⟨D.axis_le hp, by simpa using (show {p} ∈ D.complex.faces from D.axis_le hp)⟩
  have hpzero := (haxis p hpstar).mp (D.axis.vertices_subset_space hp)
  have hvzero : ∀ j : Fin 2, C.chart (D.inverse p) j.castSucc = 0 := by
    intro j
    fin_cases j
    · exact hpzero.2.1
    · exact hpzero.2.2
  have hgeom := original_vertex_coordinate_faces D.complex D.homeomorph D.inverse
    D.inverse_value p (D.axis_le hp) (D.vertex_mem_interior_core p hp) C.chart
    (by convert hC using 1; congr 3; exact Subsingleton.elim _ _)
    (by convert hface using 1; congr 2; exact Subsingleton.elim _ _) hvzero
  have hZ : {z | z ∈ V.space ∧ C.chart (D.inverse z) 0 = 0 ∧
      C.chart (D.inverse z) 1 = 0} = V.space ∩ D.axis.space := by
    ext z
    constructor
    · rintro ⟨hz, hz0, hz1⟩
      exact ⟨hz, (haxis z (D.vertex_dual_subset_star p hp hz)).mpr
        ⟨interior_subset (hcore (D.inverse z).property), hz0, hz1⟩⟩
    · rintro ⟨hz, ha⟩
      exact ⟨hz, ((haxis z (D.vertex_dual_subset_star p hp hz)).mp ha).2⟩
  dsimp only at hgeom ⊢
  dsimp only [V] at hZ
  convert hgeom using 1 <;> simp only [← hZ]
  · apply Iff.of_eq
    congr 12
    exact Subsingleton.elim _ _
  · apply forall_congr'
    intro j
    apply forall_congr'
    intro b
    apply Iff.of_eq
    congr 12 <;> exact Subsingleton.elim _ _

end PoincareConjecture.M76.Dehn.Annuli
