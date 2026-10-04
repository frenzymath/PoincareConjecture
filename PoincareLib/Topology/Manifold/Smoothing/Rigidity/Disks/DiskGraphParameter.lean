import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceDiskPairCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLInverse
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierSubcomplex
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLImageTriangulation

/-!
# Exact graph images and parameters of an original proper disk

The same original-chart graph map gives finite images of the entire
disk and rim. Its actual finite PL inverse recovers every original
parameter. The original frontier meets this disk image in exactly
the rim image. See Hudson pp. 12--19 and rigidity derivation014,
section1; no collar or graph-ambient manifold is inferred.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- A fixed injective original-chart PL graph map retains the whole
proper disk, its exact old-boundary intersection and a finite PL
inverse with the original disk parameters. See rigidity014, section1. -/
theorem exists_proper_disk_graph_parameter
    {X G ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (F : X → G)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFinj : InjOn F R) :
    ∃ (P T : SimplicialComplex ℝ G) (b : D ≃ₜ P.space) (u : G → V2),
      P.faces.Finite ∧ T.faces.Finite ∧
      P.space = F '' (j '' D) ∧ T.space = F '' (j '' Q) ∧
      b.IsFinitePL ∧ (∀ z : D, (b z : G) = F (j z)) ∧
      FinitePiecewiseAffineOn u P.space ∧
      (∀ z : D, u (F (j z)) = (z : V2)) ∧
      P.space ∩ F '' frontier R = T.space := by
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  let J := K.frontierSubcomplex D
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hJQ : J.space = Q := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
      frontier_closedBall _ one_ne_zero]
  have hjK : PolyhedralPLInCharts e j K.space := hKD.symm ▸ hj
  have hjJ : PolyhedralPLInCharts e j J.space :=
    hj.restrict_finite J hJ (hJQ.subset.trans sphere_subset_closedBall)
  have hfD : FinitePiecewiseAffineOn (F ∘ j) D := by
    simpa only [hKD] using hjK.finitePiecewiseAffineOn_comp K hK hF
  have hfQ : FinitePiecewiseAffineOn (F ∘ j) Q := by
    simpa only [hJQ] using hjJ.finitePiecewiseAffineOn_comp J hJ hF
  have hinj : InjOn (F ∘ j) D := by
    intro x hx y hy hxy
    have hjxy : j x = j y := hFinj (hDR hx) (hDR hy) hxy
    exact congrArg Subtype.val (hemb.injective
      (show (fun z : D => j z) ⟨x, hx⟩ = (fun z : D => j z) ⟨y, hy⟩ from hjxy))
  obtain ⟨P, hP, hPs⟩ := hfD.exists_finite_triangulation_image
  obtain ⟨T, hT, hTs⟩ := hfQ.exists_finite_triangulation_image
  obtain ⟨b0, hb0, hb0val⟩ := hfD.exists_homeomorph_image hinj
  let b : D ≃ₜ P.space := b0.trans (Homeomorph.setCongr hPs.symm)
  have hb : b.IsFinitePL := hb0.trans (Homeomorph.isFinitePL_setCongr hPs.symm P hP hPs)
  have hbval (z : D) : (b z : G) = F (j z) := hb0val z
  obtain ⟨u, hu, huval⟩ := hb.symm
  have huj (z : D) : u (F (j z)) = (z : V2) := by
    have h := huval (b z)
    rw [b.symm_apply_apply, hbval] at h
    exact h.symm
  have hPs' : P.space = F '' (j '' D) := by rw [hPs, image_comp]
  have hTs' : T.space = F '' (j '' Q) := by rw [hTs, image_comp]
  refine ⟨P, T, b, u, hP, hT, hPs', hTs', hb, hbval, hu, huj, ?_⟩
  rw [hPs', hTs']
  ext w
  constructor
  · rintro ⟨⟨x, ⟨z, hz, rfl⟩, rfl⟩, y, hy, hyz⟩
    have hyj : y = j z := hFinj (he.closed.frontier_subset hy) (hDR hz) hyz
    have hzQ : z ∈ Q := (hproper ⟨z, hz⟩).mp (hyj ▸ hy)
    exact ⟨j z, ⟨z, hzQ, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨j z, ⟨z, sphere_subset_closedBall hz, rfl⟩, rfl⟩, ?_⟩
    exact ⟨j z, (hproper ⟨z, sphere_subset_closedBall hz⟩).mpr hz, rfl⟩

end PoincareMT.M76
