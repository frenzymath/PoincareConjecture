import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleLifts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteCircleRegularValues
import PoincareConjecture.Proofs.M76.Rigidity.CircleSlabInterior










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩





theorem exists_hamiltonZero_regular_circle_slab {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ a ∈ Ioo ((4 * 16 : ℝ) / 4) ((4 * 16 : ℝ) / 3),
      ∃ b ∈ Ioo (2 * (4 * 16 : ℝ) / 3) (3 * (4 * 16 : ℝ) / 4),
        0 < a ∧ a < b ∧ b < 4 * 16 ∧
        let q := hamiltonZeroCircleMap phi
        let R := q ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
        let S := q ⁻¹' {(a : C0), (b : C0)}
        IsCompact (q ⁻¹' {(a : C0)}) ∧ (q ⁻¹' {(a : C0)}).Nonempty ∧
        IsCompact (q ⁻¹' {(b : C0)}) ∧ (q ⁻¹' {(b : C0)}).Nonempty ∧
        Disjoint (q ⁻¹' {(a : C0)}) (q ⁻¹' {(b : C0)}) ∧
        IsCompact R ∧ PLDomain e R ∧ frontier R = S ∧
        IsCompact (interior R)ᶜ ∧ PLDomain e (interior R)ᶜ ∧
        frontier (interior R)ᶜ = S ∧
        (interior R).Nonempty ∧ (interior (interior R)ᶜ).Nonempty ∧
        ∀ c ∈ ({(a : C0), (b : C0)} : Set C0), ∀ x : X0, q x = c →
          ∃ (d0 : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
            (G : OpenPartialHomeomorph X0 V3),
            (d0 : C0) = c ∧ ell.contLinear v = 1 ∧
            x ∈ G.source ∧ ell (G x) = 0 ∧
            (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
            (∀ y ∈ G.source, q y = ((ell (G y) + d0 : ℝ) : C0)) ∧
            ∀ y ∈ G.source, q y = c ↔ ell (G y) = 0 := by
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let q := hamiltonZeroCircleMap phi
  have hq : Function.Surjective q := surjective_hamiltonZeroCircleMap phi F
  obtain ⟨Z, hZ, hreg⟩ := OpenPartialHomeomorph.exists_finite_exceptional_circle_values
    e hphi.source_domain.compatible (4 * (16 : ℝ)) q
    (exists_hamiltonZeroCircleMap_lift e d hd phi hphi)
  obtain ⟨a, haI, b, hbI, haZ, hbZ, ha, hab, hb⟩ :=
    AddCircle.exists_two_representatives_avoiding_finite (4 * (16 : ℝ)) hZ
  have hregular : ∀ c ∈ ({(a : C0), (b : C0)} : Set C0), ∀ x : X0, q x = c →
      ∃ (d0 : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
        (G : OpenPartialHomeomorph X0 V3),
        (d0 : C0) = c ∧ ell.contLinear v = 1 ∧
        x ∈ G.source ∧ ell (G x) = 0 ∧
        (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, q y = ((ell (G y) + d0 : ℝ) : C0)) ∧
        ∀ y ∈ G.source, q y = c ↔ ell (G y) = 0 := by
    intro c hc x hx
    apply hreg c ?_ x hx
    rcases hc with hc | hc
    · rw [hc]
      exact haZ
    · rw [hc]
      exact hbZ
  obtain ⟨hR, he, hfront⟩ := circle_slab_PLDomain e hphi.source_domain.cover
    hphi.source_domain.compatible (4 * (16 : ℝ)) q ha hab hb hregular
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
  refine ⟨a, haI, b, hbI, ha, hab, hb, hcompact _, hnonempty _,
    hcompact _, hnonempty _, hdisjoint, hR, he, hfront,
    isOpen_interior.isClosed_compl.isCompact, he.closed_exterior,
    he.frontier_closed_exterior.trans hfront, ?_, ?_, hregular⟩
  · exact circle_slab_interior_nonempty (4 * (16 : ℝ)) q hq ha hab hb
  · exact circle_slab_exterior_interior_nonempty (4 * (16 : ℝ)) q hq ha hb

end PoincareConjecture.M76
