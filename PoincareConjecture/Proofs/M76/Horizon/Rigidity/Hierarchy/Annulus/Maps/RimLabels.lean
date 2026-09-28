import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SourceBoundaryPhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.TerminalAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import Mathlib.Topology.Separation.Connected

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem exists_hamiltonZero_annulus_rim_labels
    (phi : C(H0, H0)) {R S : Set X0} {alpha beta : C0}
    (hfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {alpha, beta})
    (H : Ann ≃ₜ S)
    (hrim : ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
        (H z : X0) ∈ frontier R) :
    ∃ label : Bool → Bool, ∀ side : Bool, ∀ z : Circle,
      hamiltonZeroCircleMap phi (H (Dehn.annulusRimPoint side z)) =
        if label side then beta else alpha := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hside (side : Bool) : ∃ b : Bool, ∀ z : Circle,
      hamiltonZeroCircleMap phi (H (Dehn.annulusRimPoint side z)) =
        if b then beta else alpha := by
    let f : Circle → C0 := fun z => hamiltonZeroCircleMap phi (H (Dehn.annulusRimPoint side z))
    have hf : Continuous f := (hamiltonZeroCircleMap phi).continuous.comp
      (continuous_subtype_val.comp (H.continuous.comp (Dehn.continuous_annulusRimPoint side)))
    have hpair (z : Circle) : f z ∈ ({alpha, beta} : Set C0) := by
      apply hfront
      apply (hrim _).mp
      rw [Dehn.depth_annulusRimPoint]
      cases side <;> simp
    have hfin : (range f).Finite := ((finite_singleton beta).insert alpha).subset (by
      rintro _ ⟨z, rfl⟩
      exact hpair z)
    have hconstant (z : Circle) : f z = f 0 := by
      by_contra hne
      exact ((isPreconnected_range hf).infinite_of_nontrivial
        ⟨f z, mem_range_self z, f 0, mem_range_self 0, hne⟩) hfin
    rcases hpair 0 with ha | hb
    · exact ⟨false, fun z => (hconstant z).trans ha⟩
    · exact ⟨true, fun z => (hconstant z).trans hb⟩
  choose label hlabel using hside
  exact ⟨label, hlabel⟩

end PoincareConjecture.M76
