import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonBoundedPuncturedImmersion
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# The literal period512 lattice for the original lower-handle source

The wider period retains the complete doubled core while allowing a
compact transverse image for the punctured immersion. The coordinate
quotient identification is literal and retains the half-period puncture.
See Hamilton 1976, p.66 and M76 derivation343.
-/

set_option autoImplicit false

open Set Module

namespace PoincareMT.M76

/-- The fixed free-coordinate lattice used for both original lower
handles. See Hamilton p.66 and M76 derivation343. -/
def hamiltonLowerPeriodLattice (κ : Type*) : Submodule ℤ (κ → ℝ) :=
  Submodule.pi univ fun _ =>
    (AddSubgroup.zmultiples (4 * (128 : ℝ))).toIntSubmodule

variable (κ : Type*) [Fintype κ]

private noncomputable def lowerPeriodBasis : Basis κ ℝ (κ → ℝ) :=
  (Pi.basisFun ℝ κ).unitsSMul fun _ =>
    Units.mk0 (4 * (128 : ℝ)) (by norm_num)

private theorem lowerPeriodBasis_repr (x : κ → ℝ) (i : κ) :
    (lowerPeriodBasis κ).repr x i = (1 / 512 : ℝ) * x i := by
  simp [lowerPeriodBasis, Basis.repr_unitsSMul, Pi.basisFun_repr, Units.smul_def]
  norm_num

private theorem lowerPeriodLattice_eq_span :
    hamiltonLowerPeriodLattice κ = Submodule.span ℤ (range (lowerPeriodBasis κ)) := by
  ext x
  rw [(lowerPeriodBasis κ).mem_span_iff_repr_mem ℤ x]
  change (∀ i ∈ (univ : Set κ),
    x i ∈ AddSubgroup.zmultiples (4 * (128 : ℝ))) ↔ _
  simp only [mem_univ, forall_const, AddSubgroup.mem_zmultiples_iff,
    lowerPeriodBasis_repr, mem_range]
  constructor
  · intro hx i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    change (n : ℝ) = (1 / 512 : ℝ) * x i
    rw [← hn, zsmul_eq_mul]
    ring
  · intro hx i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    change (n : ℝ) = (1 / 512 : ℝ) * x i at hn
    rw [zsmul_eq_mul]
    nlinarith

omit [Fintype κ] in
/-- The original period512 coordinate lattice is discrete.
See M76 derivation343. -/
instance [Finite κ] : DiscreteTopology (hamiltonLowerPeriodLattice κ) := by
  let : Fintype κ := Fintype.ofFinite κ
  rw [lowerPeriodLattice_eq_span]
  infer_instance

/-- The same literal lattice spans the entire free-coordinate space.
See M76 derivation343. -/
instance : IsZLattice ℝ (hamiltonLowerPeriodLattice κ) := by
  refine ⟨?_⟩
  rw [lowerPeriodLattice_eq_span]
  exact ZSpan.span_top (lowerPeriodBasis κ)

/-- The actual coordinate identification with the original product of
period512 circles. Its value on every quotient representative is literal.
See Hamilton p.66 and M76 derivation343. -/
noncomputable def hamiltonLowerLatticePiEquiv :
    ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) ≃ₜ
      (κ → AddCircle (4 * (128 : ℝ))) := by
  classical
  let m : κ → Submodule ℤ ℝ := fun _ =>
    (AddSubgroup.zmultiples (4 * (128 : ℝ))).toIntSubmodule
  let e := Submodule.quotientPi m
  refine
    { toEquiv := e.toEquiv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have hq : IsOpenQuotientMap (QuotientAddGroup.mk : (κ → ℝ) →
        (κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) :=
      QuotientAddGroup.isOpenQuotientMap_mk
    apply hq.continuous_comp_iff.mp
    change Continuous (fun x : κ → ℝ => fun i =>
      (QuotientAddGroup.mk (x i) : AddCircle (4 * (128 : ℝ))))
    exact continuous_pi fun i => QuotientAddGroup.continuous_mk.comp (continuous_apply i)
  · have hpi : IsOpenQuotientMap (fun x : κ → ℝ => fun i =>
        (QuotientAddGroup.mk (x i) : AddCircle (4 * (128 : ℝ)))) :=
      IsOpenQuotientMap.piMap (fun _ : κ => QuotientAddGroup.isOpenQuotientMap_mk)
    apply hpi.continuous_comp_iff.mp
    change Continuous (fun x : κ → ℝ =>
      e.symm (fun i => (QuotientAddGroup.mk (x i) : AddCircle (4 * (128 : ℝ)))))
    have he : (fun x : κ → ℝ =>
        e.symm (fun i => (QuotientAddGroup.mk (x i) : AddCircle (4 * (128 : ℝ))))) =
        (QuotientAddGroup.mk : (κ → ℝ) →
          (κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) := by
      funext x
      exact e.symm_apply_apply ((hamiltonLowerPeriodLattice κ).mkQ x)
    rw [he]
    exact QuotientAddGroup.continuous_mk

/-- The original quotient coordinates are retained pointwise, with no
deck translation. See M76 derivation343. -/
theorem hamiltonLowerLatticePiEquiv_mk (x : κ → ℝ) :
    hamiltonLowerLatticePiEquiv κ (QuotientAddGroup.mk x) =
      fun i => (x i : AddCircle (4 * (128 : ℝ))) := rfl

end PoincareMT.M76
