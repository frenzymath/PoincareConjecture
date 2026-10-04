import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.StandardEssentialDisk
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.EssentialOutputPolygon
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Annuli.EssentialPolygonAnnuli
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Annuli.BoundaryCorrectionTransport
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.ExactDiskParametrization
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonProtectedGeometricInputs

/-!
# Proper Dehn disks with the whole prescribed boundary map

The original boundary annulus detects an essential output of the marked
loop theorem. Planar nesting supplies two actual annuli with a common
outer rim, and separated collar graphs correct that disk to the prescribed
circle. Finally the finite PL ball-pair extension restores every original
boundary value. See Hatcher 2014, Corollary 3.2, printed p.57, and Hamilton
1976, printed p.67; M76 derivations337/338.
-/

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem annulusChartImage_middle_circle
    {X : Type*} [TopologicalSpace X] {S T : Set X} {L d : ℝ}
    (hST : S ⊆ T) (c : squareAnnulus L d ≃ₜ T)
    (hcore : ∀ p, (c p : X) ∈ S ↔ depth L p = 0) :
    annulusChartImage c (frontier (_root_.Dehn.annulusSquare L 0)) = S := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hcore p).mpr ((_root_.Dehn.mem_frontier_annulusSquare_iff L 0 p).mp hp)
  · intro hx
    let p := c.symm ⟨x, hST hx⟩
    have hp : (c p : X) = x := congrArg Subtype.val (c.apply_symm_apply ⟨x, hST hx⟩)
    refine ⟨p, ?_, hp⟩
    exact (_root_.Dehn.mem_frontier_annulusSquare_iff L 0 p).mpr
      ((hcore p).mp (hp.symm ▸ hx))

/-- Dehn's proper disk conclusion from the original compact standard PL
domain and its actual continuous filling, fixing the entire given rim map. -/
theorem exists_standard_proper_disk
    {R S : Set V3} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hS : S ⊆ frontier R) (gamma : Q2 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (f : C(D2, R))
    (hboundary : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) :
    ∃ (D : Set V3) (b : D2 ≃ₜ D),
      IsCompact D ∧ D ⊆ R ∧ b.IsFinitePL ∧
      (∀ x : Q2, (b ⟨x, sphere_subset_closedBall x.property⟩ : V3) = (gamma x : V3)) ∧
      ∀ x : D2, (b x : V3) ∈ frontier R ↔ (x : V2) ∈ Q2 := by
  obtain ⟨T, c, hTB, hST, hc, hcore, j, rim, hj, hi, hjR, hjb, _, hje, hdepth⟩ :=
    exists_standard_essential_boundary_disk hR he hS gamma hgamma f hboundary
  obtain ⟨n, P, hP, hPi, _, htransport, hinner, houter⟩ :=
    exists_essential_output_polygon c hc j hj hi rim hjb hje hdepth
  obtain ⟨a₀, a₁, ha₀, ha₁, hA₀, hA₁, h₀inner, h₁inner, h₀outer, h₁outer⟩ :=
    exists_essential_polygon_annuli P hP hPi
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : 4 * (1 / 8 : ℝ) < 1)
      hinner houter
  have hB : IsFinitePLBallPair (ℝ × ℝ) (j '' D2)
      (annulusChartImage c (P.boundary ℝ)) := by
    rw [htransport]
    exact ((isFinitePLBallPair_unit_cube (ι := Fin 2)).image hj hi).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨D, hD, hDR, hfront⟩ := exists_proper_disk_boundary_correction_through_annulus
    hR he c hc hTB hA₀ hA₁ a₀ a₁ ha₀ ha₁ h₀inner h₁inner h₀outer h₁outer
    hB (image_subset_iff.mpr hjR)
  have hmiddle := annulusChartImage_middle_circle hST c hcore
  rw [hmiddle] at hD hfront
  have hDV : IsFinitePLBallPair V2 D S :=
    hD.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨b, hb, hbvalues, hbproper⟩ :=
    exists_exact_proper_disk_parametrization hDV hfront gamma hgamma
  exact ⟨D, b, hDV.isCompact, hDR, hb, hbvalues, hbproper⟩

end PoincareMT.M76.Dehn

namespace PoincareMT.M76

/-- The unchanged standard proper-disk clause is constructed from its
original universally quantified data, with no boundary-annulus supplier. -/
theorem hasHamiltonStandardProperDehnDisks : HasHamiltonStandardProperDehnDisks := by
  intro R hR he S hS gamma hgamma f hboundary
  exact Dehn.exists_standard_proper_disk hR he hS gamma hgamma f hboundary

end PoincareMT.M76
