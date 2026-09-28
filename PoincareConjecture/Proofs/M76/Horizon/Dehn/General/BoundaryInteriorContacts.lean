import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorMovedVertices
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorMovedEdges
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BoundaryContactFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalBranchCharts









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
theorem OriginalGeneralPositionData.boundary_interior_contact_chart
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
    (p : V3) (hpB : p ∈ B.space) (hpJ : p ∈ interior J.space)
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
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  let region : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap)
  have hparam (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior J.space)
      (hxR : 0 < region x) :
      history.parameter x ∈ interior (history.parameter '' K.space) := by
    have hn : history.parameter x ∉ sphere (0 : V2) 1 :=
      fun h => hxR.ne' ((history.parameter_rim x hx).mpr h)
    have hball : history.parameter x ∈ ball (0 : V2) 1 :=
      mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp (history.parameter_inside hx))
        (fun heq => hn (mem_sphere.mpr heq)))
    exact (clipped_disk_parameter_interior data.initial.map
      (continuousOn_iff_continuous_domRestrict.mpr data.initial.embedding.continuous)
      (w.right.trans Q) K.space J.space history.parameter history.sheet_space
      history.parameter_inside history.parameter_right history.parameter_left x hx hxJ).2 hball
  have happroach (x : V3) (hx : x ∈ K.space) (hxJ : x ∈ interior J.space)
      (hxR : 0 < region x) (hx0 : ell x = 0) :
      x ∈ closure (K.space ∩ {y | 0 < ell y}) :=
    (data.boundary_interior_signed_approach step a w c Q J K hJQ hQPL hQzero
      history.sheet_space hplane hbad x hx hxJ hxR hx0).1
  have hcases := boundary_motion_interior_contact_cases J K B hK history.parameter
    history.parameter_affine history.parameter_injective ell region hparam H hHK
    (history.region_height 1) history.zero_faces history.endpoint_faces happroach
    p hpB hpJ hpR hpzero
  rcases hcases with ⟨v, hvK, _hv0, rfl⟩ | ⟨edge, heK, he2, hezero, henew, hp⟩ | hfree
  · have hvB : H.map 1 v ∈ B.vertices := by
      have hBi : B = hHK.embeddedImage (H.map 1).injective.injOn := by
        ext1
        exact history.endpoint_faces.trans (hHK.embeddedImage_faces _).symm
      rw [hBi, hHK.embeddedImage_vertices]
      exact mem_image_of_mem (H.map 1) hvK
    exact data.boundary_moved_vertex_crossing step a w c Q J C₀ B q ε H history
      hJQ hQPL hQzero hplane hbad (H.map 1 v) hvB hpJ hpR hpzero O hO hpO
  · obtain ⟨T, hpT, hTs, hTzero, hTPL, hTK, hheight⟩ :=
      data.boundary_moved_edge_crossing step a w c Q J C₀ B q ε H history
        hJQ hQPL hQzero hplane hbad edge heK he2 hezero henew p hp hpJ hpR O hO hpO
    obtain ⟨T', hT's, hT'zero, hT'PL, hT'height, hT'K⟩ :=
      exists_swapped_carrier_chart B.space (fun x => (c x).2) T hTPL hTK hheight
    exact ⟨T', hT's.symm ▸ hpT, hT's.subset.trans hTs, hT'zero p hTzero,
      hT'PL, hT'height, hT'K⟩
  · obtain ⟨T, hpT, hTs, hTzero, hTPL, _hTinv, hTK, hheight⟩ := hfree O hO hpO
    obtain ⟨T', hT's, hT'zero, hT'PL, hT'height, hT'K⟩ :=
      exists_swapped_carrier_chart B.space ell T hTPL hTK (fun x hx => (hheight x hx).symm)
    exact ⟨T', hT's.symm ▸ hpT, hT's.subset.trans hTs, hT'zero p hTzero,
      hT'PL, hT'height, hT'K⟩

end Geometry.OriginalPLTower

