import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ThreeTorusPunctureEnd
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# The exact period64 lattice in the zero handle

The literal coordinate lattice has the product circles used by the
checked punctured immersion as its quotient. The homeomorphism retains
the quotient formula, the origin and the original half-period puncture.
See Hamilton 1976, p.66 and M76 derivation331.
-/

set_option autoImplicit false

open Set Module

namespace PoincareMT.M76

/-- The actual coordinate period64 lattice of the checked punctured
three-torus. The same submodule is used by the lattice-handle quotient.
See Hamilton p.66 and derivation331. -/
def hamiltonZeroPeriodLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.pi univ fun _ =>
    (AddSubgroup.zmultiples (4 * (16 : ℝ))).toIntSubmodule

private noncomputable def zeroPeriodBasis : Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).unitsSMul fun _ =>
    Units.mk0 (4 * (16 : ℝ)) (by norm_num)

private theorem zeroPeriodBasis_repr (x : Fin 3 → ℝ) (i : Fin 3) :
    zeroPeriodBasis.repr x i = (1 / 64 : ℝ) * x i := by
  simp [zeroPeriodBasis, Basis.repr_unitsSMul, Pi.basisFun_repr, Units.smul_def]
  norm_num

private theorem zeroPeriodLattice_eq_span :
    hamiltonZeroPeriodLattice = Submodule.span ℤ (range zeroPeriodBasis) := by
  ext x
  rw [zeroPeriodBasis.mem_span_iff_repr_mem ℤ x]
  change (∀ i ∈ (univ : Set (Fin 3)),
    x i ∈ AddSubgroup.zmultiples (4 * (16 : ℝ))) ↔ _
  simp only [mem_univ, forall_const, AddSubgroup.mem_zmultiples_iff,
    zeroPeriodBasis_repr, mem_range]
  constructor
  · intro hx i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    change (n : ℝ) = (1 / 64 : ℝ) * x i
    rw [← hn, zsmul_eq_mul]
    ring
  · intro hx i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    change (n : ℝ) = (1 / 64 : ℝ) * x i at hn
    rw [zsmul_eq_mul]
    nlinarith

/-- The literal period64 coordinate lattice is discrete, as follows
from its scaled real basis. See derivation331. -/
instance : DiscreteTopology hamiltonZeroPeriodLattice := by
  rw [zeroPeriodLattice_eq_span]
  infer_instance

/-- The literal period64 coordinate lattice spans the entire source
space over the reals. See derivation331. -/
instance : IsZLattice ℝ hamiltonZeroPeriodLattice := by
  refine ⟨?_⟩
  rw [zeroPeriodLattice_eq_span]
  exact ZSpan.span_top zeroPeriodBasis

private noncomputable def zeroLatticePiEquiv :
    ((Fin 3 → ℝ) ⧸ hamiltonZeroPeriodLattice.toAddSubgroup) ≃ₜ
      (Fin 3 → StableTorus.Circle) := by
  let m : Fin 3 → Submodule ℤ ℝ := fun _ =>
    (AddSubgroup.zmultiples (4 * (16 : ℝ))).toIntSubmodule
  let e := Submodule.quotientPi m
  refine
    { toEquiv := e.toEquiv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have hq : IsOpenQuotientMap (QuotientAddGroup.mk : (Fin 3 → ℝ) →
        (Fin 3 → ℝ) ⧸ hamiltonZeroPeriodLattice.toAddSubgroup) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    apply hq.continuous_comp_iff.mp
    change Continuous (fun x : Fin 3 → ℝ => fun i =>
      (QuotientAddGroup.mk (x i) : StableTorus.Circle))
    exact continuous_pi fun i => QuotientAddGroup.continuous_mk.comp (continuous_apply i)
  · have hpi : IsOpenQuotientMap (fun x : Fin 3 → ℝ => fun i =>
        (QuotientAddGroup.mk (x i) : StableTorus.Circle)) :=
      IsOpenQuotientMap.piMap (fun _ : Fin 3 => QuotientAddGroup.isOpenQuotientMap_mk)
    apply hpi.continuous_comp_iff.mp
    change Continuous (fun x : Fin 3 → ℝ =>
      e.symm (fun i => (QuotientAddGroup.mk (x i) : StableTorus.Circle)))
    have he : (fun x : Fin 3 → ℝ =>
        e.symm (fun i => (QuotientAddGroup.mk (x i) : StableTorus.Circle))) =
        (QuotientAddGroup.mk : (Fin 3 → ℝ) →
          (Fin 3 → ℝ) ⧸ hamiltonZeroPeriodLattice.toAddSubgroup) := by
      funext x
      exact e.symm_apply_apply (hamiltonZeroPeriodLattice.mkQ x)
    rw [he]
    exact QuotientAddGroup.continuous_mk

private def zeroCircleProductEquiv :
    (Fin 3 → StableTorus.Circle) ≃ₜ
      ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle) where
  toFun x := ((x 0, x 1), x 2)
  invFun z := ![z.1.1, z.1.2, z.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_apply 0).prodMk (continuous_apply 1)).prodMk
    (continuous_apply 2)
  continuous_invFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_fst.fst
    · exact continuous_fst.snd
    · exact continuous_snd

/-- The marked homeomorphism from the actual period64 lattice quotient
to the product-circle torus used by the checked immersion. It has the
literal coordinate quotient formula. See Hamilton p.66 and derivation331. -/
noncomputable def hamiltonZeroLatticeProductEquiv :
    ((Fin 3 → ℝ) ⧸ hamiltonZeroPeriodLattice.toAddSubgroup) ≃ₜ
      ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle) :=
  zeroLatticePiEquiv.trans zeroCircleProductEquiv

/-- The lattice-to-product identification uses the same actual three
quotient coordinates, with no deck translation. See derivation331. -/
theorem hamiltonZeroLatticeProductEquiv_mk (x : Fin 3 → ℝ) :
    hamiltonZeroLatticeProductEquiv (QuotientAddGroup.mk x) =
      (((x 0 : StableTorus.Circle), (x 1 : StableTorus.Circle)),
        (x 2 : StableTorus.Circle)) := rfl

/-- The class of the literal half-period vector is the original
puncture chosen by the checked immersion. See derivation331. -/
theorem hamiltonZeroLatticeProductEquiv_puncture :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    hamiltonZeroLatticeProductEquiv
      (QuotientAddGroup.mk (fun _ : Fin 3 => (32 : ℝ))) =
      AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0 := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  rw [hamiltonZeroLatticeProductEquiv_mk, AddCircle.centeredCubeQuotient_apply]
  norm_num

end PoincareMT.M76
