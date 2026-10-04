import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Coverings.HamiltonIndexOneCoverPlacement
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonIndexOneProperDehn
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskCommonStars
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonMarkedProductCorrection
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonIndexOneCutComparison
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskProductConstruction

/-!
# The actual index-one comparison supplies the supported cover placement

Apply the named proper Dehn clause to the same comparison image,
construct one shared disk triangulation, and consume its unmarked
product through the checked marked correction and physical cuts.
The proper-disk product is constructed on that same triangulation.
See Hamilton1976, p.67 and M76 derivation357.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

open HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 1 ↪ Fin 1 ⊕ Fin 2)
local notation "Cyl" => coordinateCylinder J

variable {L : Submodule ℤ V2} [DiscreteTopology L] {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {T : HamiltonProtectedDehnAnnulus L e}
  {region : HamiltonDehnEnclosingRegion (Fin 1) (Fin 2) L e T.surface}
  {geometry : HamiltonIndexOneDehnGeometry L e T region} {A : V ≃ₜ V}

omit [DiscreteTopology L] in
/-- The same protected comparison image gives the required supported
cover placement. The actual proper disk, shared triangulation and
complete unmarked product are constructed internally. See357. -/
theorem HamiltonIndexOneProtectedImage.exists_cover_placement
    (image : HamiltonIndexOneProtectedImage geometry A)
    (dehn : HasHamiltonStandardProperDehnDisks) :
    ∃ Q : V ≃ₜ V,
      FinitePiecewiseAffineOn Q (closedBall (0 : V) 1) ∧
      (∀ x : V, 2 ≤ ‖x‖ → Q x = x) ∧
      EqOn Q id (Cylᶜ ∪ frontier Cyl) ∧
      MapsTo Q (closedBall (0 : V) 1) (A '' geometry.Psum) := by
  classical
  have hAf : EqOn (coverConjugate A) id (frontier squareBlock) :=
    fun _ hx => image.fixed_exterior hx.2
  obtain ⟨marked, boundary, D, b, hm, hmfix, he, heinner, heouter,
    _, hDR, hb, _, hboundary, hproper⟩ :=
    exists_actual_marked_proper_dehn_disk dehn (coverConjugate A) image.block_image hAf
      image.ball image.subset_box image.annulus_compact.isClosed image.boundary_contact
      image.annulus_contact image.tau image.tau_PL image.tau_fix
      image.unitParameter image.unitParameter_PL image.tau_unitParameter
      image.core_subset image.core_disjoint
  let l : W ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let a := l.toContinuousAffineEquiv
  obtain ⟨hR, hregular, _⟩ := complementaryRegion_geometry
    image.ball.isCompact.isClosed (image.ball.closure_interior_of_finrank_eq rfl)
    image.subset_box image.annulus_compact.isClosed
    (image.ball.frontier_eq_of_finrank_eq rfl) image.boundary_contact image.annulus_contact
  obtain ⟨_, hDomain⟩ := plDomain_affineImage_complementaryRegion a
    image.ball.isCompact.isClosed (image.ball.closure_interior_of_finrank_eq rfl)
    image.subset_box image.annulus_compact.isClosed
    (image.ball.frontier_eq_of_finrank_eq rfl) image.boundary_contact image.annulus_contact
    image.tau image.tau_PL image.tau_fix
  obtain ⟨triangulation⟩ := exists_proper_disk_triangulation a hDomain hR hregular
    hDR b hb hproper boundary he
  obtain ⟨unmarked⟩ := triangulation.exists_unmarked_disk_product
    (by simp [Module.finrank_prod]) hb hproper
  obtain ⟨markedProduct⟩ := exists_marked_disk_product_of_unmarked unmarked a hDomain
    hb boundary he hboundary
  obtain ⟨shell, hshell, hfrontier⟩ :=
    exists_marked_shell_map_of_disk_product markedProduct he hR
  have hinner (x : squareInnerAnnulus) (hx : (x : W) ∈ squareShell) :
      (shell ⟨x, hx⟩ : W) = marked x := by
    have hf : (x : W) ∈ frontier squareShell :=
      squareShell_frontier.symm.subset (Or.inl x.property)
    exact (hfrontier ⟨x, hf⟩ hx).trans (heinner x hf)
  have houter (x : squareOuterAnnulus) (hx : (x : W) ∈ squareShell) :
      (shell ⟨x, hx⟩ : W) = x := by
    have hf : (x : W) ∈ frontier squareShell :=
      squareShell_frontier.symm.subset (Or.inr x.property)
    exact (hfrontier ⟨x, hf⟩ hx).trans (heouter x hf)
  obtain ⟨Q, hQ, hplace, hfix⟩ := exists_supported_block_placement_of_marked_shell
    image.ball image.subset_box image.annulus_compact.isClosed image.boundary_contact
    image.annulus_contact marked hm hmfix shell hshell hinner houter
  exact exists_cover_supported_block_placement geometry.Psum A Q hQ hplace hfix

end PoincareMT.M76
