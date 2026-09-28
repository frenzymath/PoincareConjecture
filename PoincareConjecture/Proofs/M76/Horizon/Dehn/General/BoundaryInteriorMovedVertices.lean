import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryMotionHistory
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorLinkSections
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ClippedDiskParameter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.PlanarParameterLink
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.MovedVertexCrossing

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 800000 in
theorem OriginalGeneralPositionData.boundary_moved_vertex_crossing
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (a : D) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
    (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
    (J C₀ B : SimplicialComplex ℝ V3) (q : V3 → V2) (ε : ℝ)
    (H : PLCarrierMotion J.space C₀.space ε)
    (history : BoundaryMotionHistory data.initial.map (w.right.trans Q) c J C₀ B q ε H)
    (hJQ : J.space ⊆ Q.target)
    (hQPL : ∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hQzero : Q (step.projection (step.inclusion (data.initial.map a))) = 0)
    (hplane : ∀ y ∈ Q.source,
      y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
        0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0)
    (hbad : ∀ y ∈ Q.source,
      y ∈ (fun z : V2 × V2 ↦
        step.projection (step.inclusion (data.initial.map z.1))) '' data.exceptional →
      y = step.projection (step.inclusion (data.initial.map a)))
    (p : V3) (hpB : p ∈ B.vertices) (hpJ : p ∈ interior J.space)
    (hpR : 0 < (c p).1.1) (hpzero : (c p).2 = 0)
    (O : Set V3) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, (c x).2 = 0 ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, x ∈ B.space ↔ (T x).2 = 0 := by
  classical
  let K := history.sheet
  have hK : K.faces.Finite := history.ambient_finite.subset history.sheet_subcomplex
  have hHK : K.AffineOnFaces (H.map 1) :=
    fun face hface => history.motion_affine face (history.sheet_subcomplex hface)
  have hBimage : B = hHK.embeddedImage (H.map 1).injective.injOn := by
    ext1
    exact history.endpoint_faces.trans (hHK.embeddedImage_faces _).symm
  have hBvertices : B.vertices = H.map 1 '' K.vertices := by
    rw [hBimage]
    exact hHK.embeddedImage_vertices _
  obtain ⟨v, hvK, rfl⟩ := hBvertices.subset hpB
  have hvJ : v ∈ interior J.space := by
    have hi := ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
    obtain ⟨x, hx, hxeq⟩ := hi.symm.subset hpJ
    exact (H.map 1).injective hxeq ▸ hx
  have hvR : 0 < (c v).1.1 := (history.region_height 1 v) ▸ hpR
  have hvzero : (c v).2 = 0 := by
    have hs : ({v} : Finset V3) ∈ K.faces := hvK
    exact history.zero_faces {v} hs (by simpa using hpzero) v (by simp)
  have hvspace : v ∈ K.space := K.vertices_subset_space hvK
  have hparamBall : history.parameter v ∈ ball (0 : V2) 1 := by
    have hn : history.parameter v ∉ sphere (0 : V2) 1 :=
      fun h => hvR.ne' ((history.parameter_rim v hvspace).mpr h)
    exact mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp (history.parameter_inside hvspace))
      (fun heq => hn (mem_sphere.mpr heq)))
  have hparamInt : history.parameter v ∈ interior (history.parameter '' K.space) :=
    (clipped_disk_parameter_interior data.initial.map
      (continuousOn_iff_continuous_domRestrict.mpr data.initial.embedding.continuous)
      (w.right.trans Q) K.space J.space history.parameter history.sheet_space
      history.parameter_inside history.parameter_right history.parameter_left v hvspace hvJ).2
      hparamBall
  obtain ⟨n, P, hPi, hP, hPs⟩ := exists_link_polygon_of_planar_parameter K hK
    history.parameter_affine history.parameter_injective hvK hparamInt
  obtain ⟨hzeros, hpos, hneg⟩ := data.boundary_interior_link_sections step a w c Q J K
    hJQ hQPL hQzero history.sheet_space hplane hbad hK v hvK hvJ hvR hvzero
  let A := history.motion_affine.embeddedImage (H.map 1).injective.injOn
  have hA : A.faces.Finite := history.motion_affine.embeddedImage_finite
    (H.map 1).injective.injOn history.ambient_finite
  have hAs : A.space = J.space := by
    rw [history.motion_affine.embeddedImage_space, history.ambient_subdivision.space_eq]
    exact H.carrier 1
  have hBA : B ≤ A := by
    intro face hface
    obtain ⟨g, hg, rfl⟩ := history.endpoint_faces.subset hface
    exact (history.motion_affine.embeddedImage_faces _).symm.subset
      ⟨g, history.sheet_subcomplex hg, rfl⟩
  have hlink : (B.link (H.map 1 v)).space = H.map 1 '' (K.link v).space := by
    rw [hBimage]
    exact hHK.embeddedImage_link_space (H.map 1).injective.injOn hvK
  exact exists_moved_zero_vertex_crossing K B A hK hA hBA (H.map 1) hHK
    (H.map 1).injective v hpB (hAs.symm ▸ hpJ) hlink c hpzero P hP hPi hPs
    hzeros hpos hneg
    (fun x hx hn => history.strict_signs x (history.sheet_subcomplex hx) hn 1)
    O hO hpO

end Geometry.OriginalPLTower
