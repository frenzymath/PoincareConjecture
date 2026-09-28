import PoincareConjecture.Proofs.M59.Mathlib.OpenMapExtension
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RadialFamilies
import Mathlib.Topology.Order.ProjIcc










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

namespace PoincareConjecture



def m59CubeCircleDomain (n : Nat) : TopologicalSpace.Opens ((Fin n → ℝ) × LoopPlane) :=
  ⟨{p | p.2 ≠ 0}, isClosed_singleton.isOpen_compl.preimage continuous_snd⟩



def m59CubeCircleInclusion (n : Nat) : C((Fin n → I) × LoopCircle, m59CubeCircleDomain n) :=
  ⟨fun p => ⟨(fun i => (p.1 i : ℝ), p.2.val), by
      change p.2.val ≠ 0
      intro hz
      simpa only [hz, norm_zero, zero_ne_one] using p.2.property⟩, by
    exact ((continuous_pi fun i => continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_fst)).prodMk continuous_snd.subtype_val).subtype_mk _⟩



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



theorem m59CubeCircleRetraction_inclusion (n : Nat) (p : (Fin n → I) × LoopCircle) :
    m59CubeCircleRetraction n (m59CubeCircleInclusion n p) = p := by
  apply Prod.ext
  · funext i
    exact projIcc_val zero_le_one (p.1 i)
  · apply Subtype.ext
    exact Proofs.M58.radialNormalization_of_norm_eq_one p.2.property

end PoincareConjecture
