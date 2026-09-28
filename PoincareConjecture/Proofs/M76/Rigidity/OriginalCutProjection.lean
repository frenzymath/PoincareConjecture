import PoincareConjecture.Proofs.M76.Rigidity.MeridianParameter
import PoincareConjecture.Proofs.M76.Rigidity.MeridianQuotient

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "S" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

theorem exists_hamiltonMeridianCutProjection (v : E → X)
    (hv : ContinuousOn v (D ×ˢ Icc 0 p))
    (himage : v '' (D ×ˢ Icc 0 p) = R)
    (hfib : ∀ z ∈ D ×ˢ Icc 0 p, ∀ w ∈ D ×ˢ Icc 0 p,
      v z = v w ↔ z.1 = w.1 ∧
        (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p) ∨ (z.2 = p ∧ w.2 = 0)))
    (hlateral : EqOn v hamiltonMeridianCutAmbientMap (S ×ˢ Icc 0 p)) :
    ∃ r : C(HamiltonMeridianClosedCut, H), Function.Surjective r ∧
      (∀ a b : HamiltonMeridianClosedCut,
        r a = r b ↔ a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
          ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
          ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0))) ∧
      (∀ a : HamiltonMeridianClosedCut, ‖(a.1 : V2)‖ = 1 →
        r a = hamiltonMeridianQuotient a) ∧
      ∀ a : HamiltonMeridianClosedCut,
        v ((a.1 : V2), (a.2 : ℝ)) =
          ((latticeHandleDomainEquiv (Fin 2) (Fin 1) L).symm (r a) : X) := by
  let i : HamiltonMeridianClosedCut → E := fun a => ((a.1 : V2), (a.2 : ℝ))
  have hi (a : HamiltonMeridianClosedCut) : i a ∈ D ×ˢ Icc 0 p :=
    ⟨a.1.property, a.2.property⟩
  have hic : Continuous i :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let vR : HamiltonMeridianClosedCut → R := fun a =>
    ⟨v (i a), himage.subset ⟨i a, hi a, rfl⟩⟩
  have hvR : Continuous vR := (hv.comp_continuous hic hi).subtype_mk _
  let Q := latticeHandleDomainEquiv (Fin 2) (Fin 1) L
  let r : C(HamiltonMeridianClosedCut, H) := ⟨Q ∘ vR, Q.continuous.comp hvR⟩
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro x
    have hx : (Q.symm x : X) ∈ v '' (D ×ˢ Icc 0 p) :=
      himage.symm.subset (Q.symm x).property
    obtain ⟨z, hz, hzx⟩ := hx
    let a : HamiltonMeridianClosedCut := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
    refine ⟨a, ?_⟩
    change Q (vR a) = x
    have hval : vR a = Q.symm x := Subtype.ext hzx
    rw [hval, Q.apply_symm_apply]
  · intro a b
    have heq : r a = r b ↔ v (i a) = v (i b) := by
      constructor
      · intro h
        change Q (vR a) = Q (vR b) at h
        exact congrArg Subtype.val (Q.injective h)
      · intro h
        change Q (vR a) = Q (vR b)
        exact congrArg Q (show vR a = vR b from Subtype.ext h)
    rw [heq, hfib (i a) (hi a) (i b) (hi b)]
    constructor
    · rintro ⟨hfirst, htime⟩
      exact ⟨Subtype.ext hfirst, htime⟩
    · rintro ⟨hfirst, htime⟩
      exact ⟨congrArg Subtype.val hfirst, htime⟩
  · intro a ha
    have hparam : vR a = hamiltonMeridianParameter (i a) := by
      apply Subtype.ext
      change v (i a) = (hamiltonMeridianParameter (i a) : X)
      rw [hamiltonMeridianParameter_val _ a.1.property]
      exact hlateral ⟨mem_sphere_zero_iff_norm.mpr ha, a.2.property⟩
    change Q (vR a) = hamiltonMeridianQuotient a
    rw [hparam]
    exact hamiltonMeridianParameter_domainEquiv a.1 a.2
  · intro a
    change v (i a) = (Q.symm (Q (vR a)) : X)
    rw [Q.symm_apply_apply]

end PoincareConjecture.M76
