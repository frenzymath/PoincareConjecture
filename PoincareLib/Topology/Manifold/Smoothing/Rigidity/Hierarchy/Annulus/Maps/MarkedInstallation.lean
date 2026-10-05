import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.RelativeDisplacement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.MarkedDisplacementExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.AmbientDisplacement
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Parameters.RimCircleCoordinates

/-!
# Installing a marked annulus endpoint in the original ambient map

The actual relative annulus homotopy gives a finite PL displacement vanishing
on both rims.  Its extension through a finite model of the entire handle fixes
the old frontier.  Target translation installs every point of the prescribed
annulus endpoint and retains the entire second-phase map.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_marked_annulus_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    {j q : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun z : Ann => j z))
    (hjR : ∀ z : Ann, j z ∈ R)
    (hrim : ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ j z ∈ frontier R)
    (hq : PolyhedralPLInCharts d q Ann)
    {v : C(Ann, X0)} (hv : ∀ z : Ann, q z = v z)
    (hphase : ∀ z : Ann, (Q0 (v z)).1.2 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2)
    (H : (⟨fun z : Ann => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩ :
      C(Ann, X0)).HomotopyRel v Dehn.annulusRims) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ z : Ann, hamiltonZeroAmbientMap psi (j z) = v z) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior R)ᶜ) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  obtain ⟨w, hw, hwphase, hwrim, hwval⟩ :=
    exists_hamiltonZero_relative_annulus_displacement hd hphi hj hq hv hphase H
  have hwdepth (z : Ann)
      (hz : depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1) : w z = 0 := by
    apply hwrim z
    rcases hz with hz | hz
    · exact Or.inl ((Dehn.range_annulusRimPoint false).symm.subset hz)
    · exact Or.inr ((Dehn.range_annulusRimPoint true).symm.subset hz)
  obtain ⟨W, hW, hWbase, hWzero, hWphase, hWoutside⟩ :=
    exists_original_retained_annulus_displacement_extension e heR hj hji
      (fun x hx => hjR ⟨x, hx⟩) hrim
      w hw (fun z hz => hwphase ⟨z, hz⟩) hwdepth
  have hWprotected (x : X0) (hx : x ∈ (interior R)ᶜ) : W x = 0 := by
    by_cases hxR : x ∈ R
    · exact hWzero x ⟨subset_closure hxR, hx⟩
    · exact hWoutside x hxR
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hformula, G, _⟩ :=
    hphi.exists_hamiltonZero_second_phase_adjustment hd F W hW hWphase hWprotected
  refine ⟨psi, hpsi, Hpsi, Fpsi, hsame, ?_, ⟨G⟩⟩
  intro z
  rw [hformula, hWbase]
  exact (hwval z).trans (hv z)

end PoincareMT.M76
