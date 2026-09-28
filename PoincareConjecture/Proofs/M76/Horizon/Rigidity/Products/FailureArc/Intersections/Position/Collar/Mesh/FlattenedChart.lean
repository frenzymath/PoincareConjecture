import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.GraphCofaces

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

noncomputable def OriginalSurfacePairChart.normalGraphChart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b) (r c : ℝ) : OpenPartialHomeomorph X E :=
  (C.chart.trans C.coordinates).transHomeomorph (CollarMesh.normalGraphCoordinates r c)

theorem OriginalSurfacePairChart.normalGraphChart_compatible
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b) (r c : ℝ) (i : ι) :
    LocallyPiecewiseAffineOn ((e i).symm.trans (C.normalGraphChart r c))
      ((e i).symm.trans (C.normalGraphChart r c)).source := by
  have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (C.compatible i)).1
  have hraw := C.forwardPL.comp h
  have hflat := ((mem_piecewiseAffineGroupoid_iff E _).mp
    (CollarMesh.normalGraphCoordinates_PL r c)).1
  have hh := hflat.comp hraw
  simp only [Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source] at hh
  simpa only [normalGraphChart, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
    preimage_inter, preimage_comp, inter_assoc, Function.comp_assoc] using hh

theorem finite_contacts_and_coface_charts_of_normal_graph
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [DecidableEq D]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3} {S T S' : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y false) (r c : ℝ)
    (hS : ∀ z ∈ (C.chart.trans C.coordinates).target,
      (C.chart.trans C.coordinates).symm z ∈ S' ↔
        (CollarMesh.normalGraphCoordinates r c z).2 = 0)
    (K : SimplicialComplex ℝ D) {g : D → X} {p q : D}
    (hpq : ({p, q} : Finset D) ∈ K.faces) (hp : g p ∉ S') (hq : g q ∉ S')
    (hcofaces : ∀ t ∈ K.faces, ({p, q} : Finset D) ⊆ t →
      MapsTo g (convexHull ℝ (t : Set D)) (C.chart.trans C.coordinates).source ∧
      ∃ A : D →ᴬ[ℝ] E,
        EqOn ((CollarMesh.normalGraphCoordinates r c) ∘ (C.chart.trans C.coordinates) ∘ g) A
          (convexHull ℝ (t : Set D))) :
    (S' ∩ (g '' convexHull ℝ ({p, q} : Set D))).Finite ∧
      HasOriginalEdgeCofaceCharts e S' K g {p, q} := by
  apply finite_contacts_and_coface_charts_of_flattened_graph K hpq (C.normalGraphChart r c)
    (C.normalGraphChart_compatible r c) ?_ hp hq hcofaces
  intro z hz
  have hh := hS ((C.chart.trans C.coordinates) z)
    ((C.chart.trans C.coordinates).map_source hz)
  change z ∈ S' ↔
    (CollarMesh.normalGraphCoordinates r c ((C.chart.trans C.coordinates) z)).2 = 0
  simpa only [(C.chart.trans C.coordinates).left_inv hz] using hh

end PoincareConjecture.M76
