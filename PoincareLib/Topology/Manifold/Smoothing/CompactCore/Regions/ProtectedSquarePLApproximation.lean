import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.PolyhedralPLDiskExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.SquareRimPolygon

/-!
# Approximate the actual protected square filling with its whole rim fixed

The literal square and rim have finite geometric complexes. Apply relative
manifold approximation to the already constructed continuous filling in
its actual open region, retaining the same map and every rim value in the
homotopy. See Wall005, construction step 2, and Hudson, pp. 15--19.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

/-- Approximate the actual disk map relative to its entire prescribed
PL rim, retaining an actual homotopy in the same protected open region. -/
theorem exists_protected_square_PL_approximation
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    {U : Set X} (hU : IsOpen U)
    (f : C(D, U)) (b : V2 → X) (hb : PolyhedralPLInCharts e b Q)
    (hboundary : ∀ x : Q, (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = b x) :
    ∃ q : V2 → X, PolyhedralPLInCharts e q D ∧ EqOn q b Q ∧ MapsTo q D U ∧
      ∃ H : C(unitInterval × D, U),
        (∀ x : D, H (0, x) = f x) ∧
        (∀ x : D, (H (1, x) : X) = q x) ∧
        ∀ (t : unitInterval) (x : Q),
          (H (t, ⟨x, sphere_subset_closedBall x.property⟩) : X) = b x := by
  classical
  let := ChartedSpace.ofChartCover e hcover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  let L := Dehn.squareRimPolygon.simplicialComplex Dehn.hasSimplicialEdges_squareRimPolygon
  have hL : L.faces.Finite :=
    Dehn.squareRimPolygon.finite_simplicialComplex_faces Dehn.hasSimplicialEdges_squareRimPolygon
  have hLQ : L.space = Q :=
    (Dehn.squareRimPolygon.simplicialComplex_space
      Dehn.hasSimplicialEdges_squareRimPolygon).trans Dehn.boundary_squareRimPolygon
  have hLK : L.space ⊆ K.space := by
    rw [hLQ, hKD]
    exact sphere_subset_closedBall
  let a : V2 → X := fun x => if hx : x ∈ D then (f ⟨x, hx⟩ : X) else b x
  have ha (x : D) : a x = (f x : X) := by simp only [a, dif_pos x.property]
  have haK : ContinuousOn a K.space := by
    rw [hKD]
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp f.continuous).congr (fun x => (ha x).symm)
  have hab : EqOn a b Q := by
    intro x hx
    exact (ha ⟨x, sphere_subset_closedBall hx⟩).trans (hboundary ⟨x, hx⟩)
  have haL : PolyhedralPLInCharts e a L.space := by
    rw [hLQ]
    exact hb.congr hab.symm
  have haU : MapsTo a K.space U := by
    intro x hx
    have hxD : x ∈ D := hKD ▸ hx
    rw [ha ⟨x, hxD⟩]
    exact (f ⟨x, hxD⟩).property
  obtain ⟨q, hq, hqa, hqU, T, hTU, hT0, hT1, hTfix⟩ :=
    OpenPartialHomeomorph.exists_relative_polyhedralPL_approximation
      e hcompat hcover K L hK hL hLK haK haL hU haU
  let j : D → K.space := fun x => ⟨x, hKD.symm ▸ x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let H : C(unitInterval × D, U) :=
    ⟨fun z => ⟨T (z.1, j z.2), hTU (z.1, j z.2)⟩,
      (T.continuous.comp (continuous_fst.prodMk (hj.comp continuous_snd))).subtype_mk _⟩
  refine ⟨q, hKD ▸ hq, ?_, hKD ▸ hqU, H, ?_, ?_, ?_⟩
  · intro x hx
    exact (hqa (hLQ.symm ▸ hx)).trans (hab hx)
  · intro x
    exact Subtype.ext ((hT0 (j x)).trans (ha x))
  · intro x
    exact hT1 (j x)
  · intro t x
    exact (hTfix t (j ⟨x, sphere_subset_closedBall x.property⟩)
      (hLQ.symm ▸ x.property)).trans (hab x.property)

end PoincareMT.M76
