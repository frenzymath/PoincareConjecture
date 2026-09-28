import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalIncidentQuarter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.VertexFaces

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.joint_subset_vertex_link
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (v : D.sample → ℝ × V3) (hvs : v ∈ s) :
    (D.complex.barycentricDualBlock s).space ⊆
      ((D.complex.barycentricDualBlock {v}).link v).space := by
  classical
  have hstrict : ({v} : Finset (D.sample → ℝ × V3)) ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.singleton_subset_iff.mpr hvs, ?_⟩
    intro he
    have hc := congrArg Finset.card he
    simp [hcard] at hc
  simpa only [Finset.centroid_singleton, id_eq] using
    space_subset_of_le (D.complex.barycentricDualBlock_le_link_of_ssubset
      (D.axis_le (D.axis.face_subset_vertices hs hvs)) hstrict)

open Classical in

theorem ComponentBranchModel.local_incident_quarter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (v : D.sample → ℝ × V3) (hvs : v ∈ s)
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
    (signs : Fin 2 → Bool) :
    let K := D.complex.barycentricDualBlock s
    let Q := {z | z ∈ K.space ∧ ∀ j : Fin 2,
      SignedJointCross.side (signs j) (C.chart (D.inverse z) j.castSucc)}
    let U := (Q ∩ {z | C.chart (D.inverse z) 0 = 0}) ∪
      (Q ∩ {z | C.chart (D.inverse z) 1 = 0})
    let O := Q ∩ (K.link (s.centroid ℝ id)).space
    ∃ a b, a ≠ b ∧ IsFinitePLBallPair P2 Q (O ∪ U) ∧
      IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ O {a, b} ∧ U ∩ O = {a, b} ∧
      Q ⊆ (D.complex.barycentricDualBlock {v}).space ∧
      Q ⊆ ((D.complex.barycentricDualBlock {v}).link v).space := by
  classical
  obtain ⟨x0, y0, C0, J, hC0, _, _, hJ, hrim, hcoord, _, hcoface⟩ :=
    D.exists_signed_joint_cross hcore s hs hcard v hvs
  have hfin : D.complex_finite.fintype = (inferInstance : Fintype D.complex.faces) :=
    Subsingleton.elim _ _
  rw [hfin] at hJ hrim
  have hcoface' (j : Fin 2) (b : Bool) : ∃ t : Finset (D.sample → ℝ × V3),
      t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id := by
    obtain ⟨t, ht, hst, htc, he⟩ := hcoface j b
    exact ⟨t, ht.1.1, hst, htc, he⟩
  obtain ⟨swap, eta, hzero, _, hside⟩ := D.exists_incident_joint_transport hcore s hs hcard
    v v hvs hvs C0 C hC0 hC hface haxis hsheet J hJ hcoord hcoface'
  have hgeom := J.incident_quarter_geometry
    (fun j z => C.chart (D.inverse z) j.castSucc) swap eta signs hzero hside
  dsimp only at hgeom ⊢
  rw [hJ, hrim] at hgeom
  obtain ⟨a, b, hab, hQ, hU, hO, hUO⟩ := hgeom
  refine ⟨a, b, hab, hQ, hU, hO, hUO, ?_, ?_⟩
  · exact fun _ hz => space_subset_of_le (D.complex.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hvs)) hz.1
  · exact fun _ hz => D.joint_subset_vertex_link s hs hcard v hvs hz.1

end PoincareConjecture.M76.Dehn.Annuli
