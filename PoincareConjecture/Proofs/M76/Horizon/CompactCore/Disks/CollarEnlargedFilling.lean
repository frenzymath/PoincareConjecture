import PoincareConjecture.Proofs.M76.Mathlib.RadialBallQuotient
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

noncomputable def halfSourceSquare : C(D, D) :=
  ⟨fun x => ⟨(1 / 2 : ℝ) • (x : V2), by
    have hx : ‖(x : V2)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    rw [mem_closedBall, dist_zero_right, norm_smul]
    norm_num
    linarith⟩, by fun_prop⟩

noncomputable def outerHalfSquare : C(Q × I, D) :=
  (unitSphereRadialMap V2).comp
    ⟨fun z => (⟨(1 + (z.2 : ℝ)) / 2, by
      constructor <;> linarith [z.2.property.1, z.2.property.2]⟩, z.1), by fun_prop⟩

theorem exists_collar_enlarged_square_parameter
    {E : Type*} [TopologicalSpace E] [T2Space E] {B : Set E}
    (d : D ≃ₜ B) (c : C(Q × I, E)) (hc : Function.Injective c)
    (hbase : ∀ u : Q, c (u, 0) = (d ⟨u, sphere_subset_closedBall u.property⟩ : E))
    (hout : ∀ (u : Q) (t : I), 0 < (t : ℝ) → c (u, t) ∉ B) :
    ∃ r : C(↥(B ∪ range c), D),
      (∀ x : D, r ⟨d x, Or.inl (d x).property⟩ = halfSourceSquare x) ∧
      (∀ z : Q × I, r ⟨c z, Or.inr (mem_range_self z)⟩ = outerHalfSquare z) ∧
      ∀ u : Q, r ⟨c (u, 1), Or.inr (mem_range_self (u, 1))⟩ =
        ⟨u, sphere_subset_closedBall u.property⟩ := by
  let q : C(D ⊕ (Q × I), ↥(B ∪ range c)) :=
    ⟨Sum.elim (fun x => ⟨d x, Or.inl (d x).property⟩)
      (fun z => ⟨c z, Or.inr (mem_range_self z)⟩),
      ((continuous_subtype_val.comp d.continuous).subtype_mk _).sumElim
        (c.continuous.subtype_mk _)⟩
  have hqsurj : Function.Surjective q := by
    intro x
    rcases x.property with hx | hx
    · exact ⟨Sum.inl (d.symm ⟨x, hx⟩), Subtype.ext
        (congrArg (Subtype.val : B → E) (d.apply_symm_apply ⟨x, hx⟩))⟩
    · obtain ⟨z, hz⟩ := hx
      exact ⟨Sum.inr z, Subtype.ext hz⟩
  have hq : Topology.IsQuotientMap q := .of_surjective_continuous hqsurj q.continuous
  let p : C(D ⊕ (Q × I), D) :=
    ⟨Sum.elim halfSourceSquare outerHalfSquare,
      halfSourceSquare.continuous.sumElim outerHalfSquare.continuous⟩
  have hseam (x : D) (z : Q × I) (hxz : (d x : E) = c z) :
      halfSourceSquare x = outerHalfSquare z := by
    have ht : z.2 = 0 := by
      apply Subtype.ext
      apply le_antisymm _ z.2.property.1
      by_contra h
      exact hout z.1 z.2 (lt_of_not_ge h) (hxz ▸ (d x).property)
    have hx : x = (⟨z.1, sphere_subset_closedBall z.1.property⟩ : D) := by
      apply d.injective
      apply Subtype.ext
      exact hxz.trans (by rw [show z = (z.1, 0) from Prod.ext rfl ht, hbase])
    apply Subtype.ext
    change (1 / 2 : ℝ) • (x : V2) = ((1 + (z.2 : ℝ)) / 2) • (z.1 : V2)
    rw [hx, ht]
    norm_num
  have hfactor : Function.FactorsThrough p q := by
    intro x y hxy
    have hv := congrArg (Subtype.val : ↥(B ∪ range c) → E) hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg halfSourceSquare (d.injective (Subtype.ext hv))
      | inr z => exact hseam x z hv
    | inr z =>
      cases y with
      | inl y => exact (hseam y z hv.symm).symm
      | inr w => exact congrArg outerHalfSquare (hc hv)
  let r := hq.lift p hfactor
  have hr (z : D ⊕ (Q × I)) : r (q z) = p z :=
    congrArg (fun f : C(D ⊕ (Q × I), D) => f z) (hq.lift_comp p hfactor)
  refine ⟨r, fun x => hr (Sum.inl x), fun z => hr (Sum.inr z), ?_⟩
  intro u
  apply (hr (Sum.inr (u, 1))).trans
  apply Subtype.ext
  change ((1 + (1 : ℝ)) / 2) • (u : V2) = (u : V2)
  norm_num

theorem exists_collar_enlarged_filling
    {E Y : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace Y]
    {B : Set E} (d : D ≃ₜ B) (c : C(Q × I, E)) (hc : Function.Injective c)
    (hbase : ∀ u : Q, c (u, 0) = (d ⟨u, sphere_subset_closedBall u.property⟩ : E))
    (hout : ∀ (u : Q) (t : I), 0 < (t : ℝ) → c (u, t) ∉ B)
    (f : C(D, Y)) {F : Set Y} (hf : ∀ x : D, f x ∉ F) :
    ∃ fill : C(↥(B ∪ range c), Y),
      (∀ x : D, fill ⟨d x, Or.inl (d x).property⟩ = f (halfSourceSquare x)) ∧
      (∀ z : Q × I, fill ⟨c z, Or.inr (mem_range_self z)⟩ = f (outerHalfSquare z)) ∧
      (∀ u : Q, fill ⟨c (u, 1), Or.inr (mem_range_self (u, 1))⟩ =
        f ⟨u, sphere_subset_closedBall u.property⟩) ∧
      ∀ x : ↥(B ∪ range c), fill x ∉ F := by
  obtain ⟨r, hrB, hrc, hr1⟩ := exists_collar_enlarged_square_parameter d c hc hbase hout
  exact ⟨f.comp r, fun x => congrArg f (hrB x), fun z => congrArg f (hrc z),
    fun u => congrArg f (hr1 u), fun x => hf (r x)⟩

end PoincareConjecture.M76
