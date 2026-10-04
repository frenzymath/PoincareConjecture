import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.MarkedLoopTheorem
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Topology.LoopClassTransport

/-!
# Preserve essentiality in the whole boundary annulus

The relatively open marked neighborhood may be smaller than its compact
annulus. Use the kernel of the map to the annulus as the original normal
subgroup in the proved loop theorem. The resulting disk boundary is then
essential in the entire annulus, as required for planar nesting.
See Hatcher 2014, Corollary 3.2, p.57; Dehn020 and Dehn022, section12.
-/

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

/-- Construct a proper embedded disk whose boundary remains nontrivial
under an actual continuous map of the original marked neighborhood. -/
theorem exists_marked_boundary_disk_with_essential_image
    {X ι Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X) (hR : PLDomain e R)
    (F : Set X) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (f : C(D2, R)) (gamma : C(Q2, F))
    (hgamma : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X))
    (u : C(F, Y))
    (hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((squareRimLoop.map gamma.continuous).map u.continuous)) ≠ 1) :
    ∃ (j : V2 → X) (rim : C(Q2, F)),
      PolyhedralPLInCharts e j D2 ∧ IsEmbedding (fun x : D2 ↦ j x) ∧ MapsTo j D2 R ∧
      (∀ x : Q2, j x = (rim x : X)) ∧
      (∀ x : D2, j x ∈ frontier R ↔ (x : V2) ∈ Q2) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((squareRimLoop.map rim.continuous).map u.continuous)) ≠ 1 := by
  let q := Path.refl (u (gamma squareRimBase))
  let phi := markedProjectionHom u q
  let J := phi.ker
  have hJ : J.Normal := inferInstance
  have hout : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ∉ J := by
    intro h
    change phi (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous))) = 1 at h
    rw [markedProjectionHom_loop] at h
    exact hessential ((q.whiskeredLoopClass_eq_one_iff _).mp h)
  obtain ⟨j, rim, hj, hi, hinside, hboundary, hproper, p, hp⟩ :=
    exists_marked_boundary_PL_loop_disk e R hR F hF hFopen f gamma hgamma J hJ hout
  refine ⟨j, rim, hj, hi, hinside, hboundary, hproper, ?_⟩
  intro hnull
  apply hp
  change phi (p.whiskeredLoopClass (squareRimLoop.map rim.continuous)) = 1
  rw [markedProjectionHom_whiskered]
  exact ((q.trans (p.map u.continuous)).whiskeredLoopClass_eq_one_iff _).mpr hnull

end PoincareMT.M76.Dehn
