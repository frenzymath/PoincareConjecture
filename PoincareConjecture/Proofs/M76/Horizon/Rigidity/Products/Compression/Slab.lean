import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleLifts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteCircleRegularValues
import PoincareConjecture.Proofs.M76.Rigidity.CircleSlabInterior








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.PrescribedSlab

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩


theorem exists_hamiltonZero_circle_slab {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (_hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (_hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 4 * 16)
    (he0 : PLDomain e ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront0 : frontier ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b) =
      (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0), (b : C0)}) :
        let q := hamiltonZeroCircleMap phi
        let R := q ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
        let S := q ⁻¹' {(a : C0), (b : C0)}
        IsCompact (q ⁻¹' {(a : C0)}) ∧ (q ⁻¹' {(a : C0)}).Nonempty ∧
        IsCompact (q ⁻¹' {(b : C0)}) ∧ (q ⁻¹' {(b : C0)}).Nonempty ∧
        Disjoint (q ⁻¹' {(a : C0)}) (q ⁻¹' {(b : C0)}) ∧
        IsCompact R ∧ PLDomain e R ∧ frontier R = S ∧
        IsCompact (interior R)ᶜ ∧ PLDomain e (interior R)ᶜ ∧
        frontier (interior R)ᶜ = S ∧
        (interior R).Nonempty ∧ (interior (interior R)ᶜ).Nonempty := by
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let q := hamiltonZeroCircleMap phi
  have hq : Function.Surjective q := surjective_hamiltonZeroCircleMap phi F
  have hR := (AddCircle.isCompact_closedIntervalArc (4 * (16 : ℝ)) a b).isClosed.preimage q.continuous
  have he := he0
  have hfront := hfront0
  have hcompact (c : C0) : IsCompact (q ⁻¹' {c}) :=
    (isClosed_singleton.preimage q.continuous).isCompact
  have hnonempty (c : C0) : (q ⁻¹' {c}).Nonempty := by
    obtain ⟨x, hx⟩ := hq c
    exact ⟨x, hx⟩
  have hdisjoint : Disjoint (q ⁻¹' {(a : C0)}) (q ⁻¹' {(b : C0)}) := by
    apply disjoint_left.mpr
    intro x hxa hxb
    have hqa : q x = (a : C0) := hxa
    have hqb : q x = (b : C0) := hxb
    have haP : a ∈ Ico (0 : ℝ) (0 + 4 * 16) := ⟨ha.le, by linarith⟩
    have hbP : b ∈ Ico (0 : ℝ) (0 + 4 * 16) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haP hbP).mp (hqa.symm.trans hqb))
  refine ⟨hcompact _, hnonempty _,
    hcompact _, hnonempty _, hdisjoint, hR.isCompact, he, hfront,
    isOpen_interior.isClosed_compl.isCompact, he.closed_exterior,
    he.frontier_closed_exterior.trans hfront, ?_, ?_⟩
  · exact circle_slab_interior_nonempty (4 * (16 : ℝ)) q hq ha hab hb
  · exact circle_slab_exterior_interior_nonempty (4 * (16 : ℝ)) q hq ha hb

end PoincareConjecture.M76.PrescribedSlab
