import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryMotionHistory
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorLinkSections
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ClippedDiskParameter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.MovedEdgeCrossing

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval
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
theorem OriginalGeneralPositionData.boundary_moved_edge_crossing
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
    (edge : Finset V3) (heK : edge ∈ history.sheet.faces) (he2 : edge.card = 2)
    (hezero : ∀ x ∈ edge, (c x).2 = 0)
    (henew : ∀ x ∈ edge, (c (H.map 1 x)).2 = 0)
    (p : V3)
    (hp : p ∈ H.map 1 '' intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (hpJ : p ∈ interior J.space) (hpR : 0 < (c p).1.1)
    (O : Set V3) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      p ∈ T.source ∧ T.source ⊆ O ∧ T p = 0 ∧
      LocallyPiecewiseAffineOn T T.source ∧
      (∀ x ∈ T.source, x ∈ B.space ↔ (T x).1.1 = 0) ∧
      ∀ x ∈ T.source, (T x).2 = (c x).2 := by
  classical
  let K := history.sheet
  have hK : K.faces.Finite := history.ambient_finite.subset history.sheet_subcomplex
  have hHK : K.AffineOnFaces (H.map 1) :=
    fun face hface ↦ history.motion_affine face (history.sheet_subcomplex hface)
  have hBimage : B = hHK.embeddedImage (H.map 1).injective.injOn := by
    ext1
    exact history.endpoint_faces.trans (hHK.embeddedImage_faces _).symm
  have hB : B.faces.Finite := by
    rw [hBimage]
    exact hHK.embeddedImage_finite (H.map 1).injective.injOn hK
  obtain ⟨z, hzedge, rfl⟩ := hp
  have hzJ : z ∈ interior J.space := by
    have hi := ((H.map 1).image_interior J.space).trans (congrArg interior (H.carrier 1))
    obtain ⟨x, hx, hxeq⟩ := hi.symm.subset hpJ
    exact (H.map 1).injective hxeq ▸ hx
  have hzR : 0 < (c z).1.1 := (history.region_height 1 z) ▸ hpR
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hzeroHull : convexHull ℝ (edge : Set V3) ⊆ {x | ell x = 0} :=
    convexHull_min hezero ((convex_singleton (0 : ℝ)).linear_preimage ell.toLinearMap)
  have hzzero : (c z).2 = 0 := hzeroHull (intrinsicInterior_subset hzedge)
  have hzspace : z ∈ K.space := K.convexHull_subset_space heK (intrinsicInterior_subset hzedge)
  have hparamBall : history.parameter z ∈ ball (0 : V2) 1 := by
    have hn : history.parameter z ∉ sphere (0 : V2) 1 :=
      fun h ↦ hzR.ne' ((history.parameter_rim z hzspace).mpr h)
    exact mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp (history.parameter_inside hzspace))
      (fun heq ↦ hn (mem_sphere.mpr heq)))
  have hparamInt : history.parameter z ∈ interior (history.parameter '' K.space) :=
    (clipped_disk_parameter_interior data.initial.map
      (continuousOn_iff_continuous_domRestrict.mpr data.initial.embedding.continuous)
      (w.right.trans Q) K.space J.space history.parameter history.sheet_space
      history.parameter_inside history.parameter_right history.parameter_left z hzspace hzJ).2
      hparamBall
  let coord := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let param := coord ∘ history.parameter
  have hparam : K.AffineOnFaces param := by
    intro face hface
    obtain ⟨A, hA⟩ := history.parameter_affine face hface
    exact ⟨coord.toContinuousLinearMap.toContinuousAffineMap.comp A,
      fun x hx ↦ congrArg coord (hA hx)⟩
  have hparami : InjOn param K.space :=
    coord.injective.comp_injOn history.parameter_injective
  have hparamInterior : param z ∈ interior (param '' K.space) := by
    have h := coord.toHomeomorph.image_interior (history.parameter '' K.space)
    change coord '' interior (history.parameter '' K.space) =
      interior (coord '' (history.parameter '' K.space)) at h
    have hm := mem_image_of_mem coord hparamInt
    rw [h] at hm
    simpa only [param, image_image, Function.comp_def] using hm
  obtain ⟨hpositive, hnegative⟩ :=
    data.boundary_interior_signed_approach step a w c Q J K hJQ hQPL hQzero
      history.sheet_space hplane hbad z hzspace hzJ hzR hzzero
  have heB : edge.image (H.map 1) ∈ B.faces := by
    rw [hBimage]
    exact (hHK.image_mem_embeddedImage_iff (H.map 1).injective.injOn
      (K.subset_space heK)).mpr heK
  have hpHull : H.map 1 z ∈ convexHull ℝ (edge.image (H.map 1) : Set V3) := by
    rw [Finset.coe_image, ← hHK.image_convexHull heK]
    exact mem_image_of_mem (H.map 1) (intrinsicInterior_subset hzedge)
  have hpInterior : H.map 1 z ∈
      intrinsicInterior ℝ (convexHull ℝ (edge.image (H.map 1) : Set V3)) := by
    obtain ⟨face, hface, hpface⟩ := B.exists_face_intrinsicInterior_of_finite hB
      (B.convexHull_subset_space heB hpHull)
    have hsub := B.subset_of_mem_intrinsicInterior_face hface heB hpface hpHull
    obtain ⟨oldFace, holdFace, rfl⟩ := history.endpoint_faces.subset hface
    have hzold : z ∈ convexHull ℝ (oldFace : Set V3) := by
      have hm := intrinsicInterior_subset hpface
      rw [Finset.coe_image, ← hHK.image_convexHull holdFace] at hm
      exact (H.map 1).injective.mem_set_image.mp hm
    have holdsub := K.subset_of_mem_intrinsicInterior_face heK holdFace hzedge hzold
    have heq := Finset.Subset.antisymm hsub (Finset.image_subset_image holdsub)
    exact heq ▸ hpface
  exact exists_moved_zero_edge_crossing K B hK (H.map 1) hHK (H.map 1).injective
    hBimage param hparam hparami edge heK he2 ell hezero henew z hzedge hparamInterior
    hpositive hnegative
    (fun x hx hn ↦ history.strict_signs x (history.sheet_subcomplex hx) hn 1)
    (H.map 1 z) hpInterior O hO hpO

end Geometry.OriginalPLTower
