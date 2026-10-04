import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.OpenMapExtension
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RadialFamilies
import Mathlib.Topology.Order.ProjIcc

/-!
# The open ambient domain for cubical loop approximation

Clamp the real cube coordinates and radially project the nonzero plane
coordinate. This extends every continuous cube-times-circle family to an
open Euclidean domain in every cube dimension. Source: MT Claim 18.16,
printed p. 430, approximation derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

namespace PoincareMT

/-- The ambient cube coordinates times the punctured plane.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
def m59CubeCircleDomain (n : Nat) : TopologicalSpace.Opens ((Fin n → ℝ) × LoopPlane) :=
  ⟨{p | p.2 ≠ 0}, isClosed_singleton.isOpen_compl.preimage continuous_snd⟩

/-- The cube times circle sits continuously in the open approximation domain.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
def m59CubeCircleInclusion (n : Nat) : C((Fin n → I) × LoopCircle, m59CubeCircleDomain n) :=
  ⟨fun p => ⟨(fun i => (p.1 i : ℝ), p.2.val), by
      change p.2.val ≠ 0
      intro hz
      simpa only [hz, norm_zero, zero_ne_one] using p.2.property⟩, by
    exact ((continuous_pi fun i => continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_fst)).prodMk continuous_snd.subtype_val).subtype_mk _⟩

/-- Continuous clamping and radial projection onto cube times circle.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
def m59CubeCircleRetraction (n : Nat) : C(m59CubeCircleDomain n, (Fin n → I) × LoopCircle) :=
  ⟨fun p => (fun i => projIcc 0 1 zero_le_one (p.val.1 i),
    ⟨Proofs.M58.radialNormalization p.val.2, Proofs.M58.norm_radialNormalization p.property⟩), by
    apply Continuous.prodMk
    · exact continuous_pi fun i => continuous_projIcc.comp
        ((continuous_apply i).comp (continuous_fst.comp continuous_subtype_val))
    · apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro p
      exact (Proofs.M58.contDiffAt_radialNormalization p.property).continuousAt.comp
        (f := fun q : m59CubeCircleDomain n => q.val.2)
        (continuous_snd.comp continuous_subtype_val).continuousAt⟩

/-- Retraction fixes every actual cube-times-circle point.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
theorem m59CubeCircleRetraction_inclusion (n : Nat) (p : (Fin n → I) × LoopCircle) :
    m59CubeCircleRetraction n (m59CubeCircleInclusion n p) = p := by
  apply Prod.ext
  · funext i
    exact projIcc_val zero_le_one (p.1 i)
  · apply Subtype.ext
    exact Proofs.M58.radialNormalization_of_norm_eq_one p.2.property

end PoincareMT
