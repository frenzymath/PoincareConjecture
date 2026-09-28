import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

open Set Metric unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_parametrized_disk_collar
    {B s : Set V2} (a : D ≃ₜ B) (hsB : s ⊆ B)
    (hrim : ∀ x : D, (a x : V2) ∈ s ↔ (x : V2) ∈ Q)
    (c : C(s × I, V2)) (hc : Topology.IsEmbedding c)
    (hbase : ∀ u : s, c (u, 0) = u)
    (hout : ∀ (u : s) (t : I), 0 < (t : ℝ) → c (u, t) ∉ B) :
    ∃ c' : C(Q × I, V2),
      (∀ (u : Q) (t : I), c' (u, t) =
        c (⟨a ⟨u, sphere_subset_closedBall u.property⟩,
          (hrim _).mpr u.property⟩, t)) ∧
      Topology.IsEmbedding c' ∧
      (∀ u : Q, c' (u, 0) = a ⟨u, sphere_subset_closedBall u.property⟩) ∧
      range c' = range c ∧
      (∀ t : I, range (fun u : Q => c' (u, t)) = range (fun u : s => c (u, t))) ∧
      (∀ (u : Q) (t : I), 0 < (t : ℝ) → c' (u, t) ∉ B) ∧
      (∀ W : Set V2, range c' ⊆ W ↔ range c ⊆ W) ∧
      ∀ E : Set V2, frontier E ⊆ range (fun u : Q => c' (u, 1)) ↔
        frontier E ⊆ range (fun u : s => c (u, 1)) := by
  let r : Q ≃ₜ s := {
    toFun := fun u => ⟨a ⟨u, sphere_subset_closedBall u.property⟩, (hrim _).mpr u.property⟩
    invFun := fun v => ⟨a.symm ⟨v, hsB v.property⟩, (hrim _).mp (by
      simpa only [a.apply_symm_apply] using v.property)⟩
    left_inv := fun u => by
      apply Subtype.ext
      change (a.symm (a ⟨u, sphere_subset_closedBall u.property⟩) : V2) = u
      exact congrArg (fun x : D => (x : V2))
        (a.symm_apply_apply ⟨u, sphere_subset_closedBall u.property⟩)
    right_inv := fun v => by
      apply Subtype.ext
      change (a (a.symm ⟨v, hsB v.property⟩) : V2) = v
      exact congrArg (fun x : B => (x : V2)) (a.apply_symm_apply ⟨v, hsB v.property⟩)
    continuous_toFun := by
      exact (continuous_subtype_val.comp (a.continuous.comp
        (continuous_subtype_val.subtype_mk _))).subtype_mk _
    continuous_invFun := by
      exact (continuous_subtype_val.comp (a.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _))).subtype_mk _ }
  let rprod : Q × I ≃ₜ s × I := r.prodCongr (Homeomorph.refl I)
  let c' : C(Q × I, V2) := c.comp ⟨rprod, rprod.continuous⟩
  have hrange : range c' = range c := by
    exact rprod.surjective.range_comp c
  have hlevel (t : I) : range (fun u : Q => c' (u, t)) =
      range (fun u : s => c (u, t)) := r.surjective.range_comp (fun u => c (u, t))
  refine ⟨c', fun _ _ => rfl, hc.comp rprod.isEmbedding,
    fun u => hbase (r u), hrange, hlevel, fun u t ht => hout (r u) t ht, ?_, ?_⟩
  · intro W
    rw [hrange]
  · intro E
    rw [hlevel]

end PoincareConjecture.M76
