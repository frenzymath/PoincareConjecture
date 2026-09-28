import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Relation

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M76.CutGraph

variable {K V I : Type*} [Field K] [Fintype V] [Fintype I]
  [DecidableEq V] [DecidableEq I]

noncomputable def incidenceBoundary (ends : I → Bool → V) : (I → K) →ₗ[K] (V → K) :=
  ∑ i, (LinearMap.proj i).smulRight
    (Pi.single (ends i true) 1 - Pi.single (ends i false) 1)

noncomputable def vertexAugmentation : (V → K) →ₗ[K] K :=
  ∑ v, LinearMap.proj v

omit [Fintype V] [DecidableEq I] in
@[simp] theorem incidenceBoundary_apply (ends : I → Bool → V) (c : I → K) :
    incidenceBoundary ends c =
      ∑ i, c i • (Pi.single (ends i true) 1 - Pi.single (ends i false) 1) := by
  simp [incidenceBoundary, LinearMap.sum_apply]

omit [DecidableEq V] in
@[simp] theorem vertexAugmentation_apply (c : V → K) :
    vertexAugmentation c = ∑ v, c v := by
  simp [vertexAugmentation, LinearMap.sum_apply]

omit [Fintype V] in
@[simp] theorem incidenceBoundary_single (ends : I → Bool → V) (i : I) :
    incidenceBoundary ends (Pi.single i (1 : K)) =
      Pi.single (ends i true) 1 - Pi.single (ends i false) 1 := by
  simp [incidenceBoundary_apply, Pi.single_apply]

omit [DecidableEq I] in
theorem incidenceBoundary_range_le :
    ∀ ends : I → Bool → V, LinearMap.range (incidenceBoundary (K := K) ends) ≤
      LinearMap.ker vertexAugmentation := by
  intro ends x hx
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mem_ker, incidenceBoundary_apply, map_sum]
  simp only [map_smul, map_sub, vertexAugmentation_apply]
  simp

omit [Fintype V] in
theorem vertex_difference_mem_range (ends : I → Bool → V) {v w : V}
    (h : Relation.EqvGen
      (fun a b => ∃ i, ends i false = a ∧ ends i true = b) v w) :
    (Pi.single w 1 : V → K) - Pi.single v 1 ∈
      LinearMap.range (incidenceBoundary ends) := by
  induction h with
  | rel a b hab =>
      obtain ⟨i, rfl, rfl⟩ := hab
      exact ⟨Pi.single i 1, incidenceBoundary_single ends i⟩
  | refl a => simp
  | symm a b _ ih =>
      simpa only [neg_sub] using
        (LinearMap.range (incidenceBoundary (K := K) ends)).neg_mem ih
  | trans a b c _ _ hab hbc =>
      convert (LinearMap.range (incidenceBoundary (K := K) ends)).add_mem hab hbc
        using 1
      abel

theorem incidenceBoundary_range_eq_ker [Nonempty V] (ends : I → Bool → V)
    (hconn : ∀ v w, Relation.EqvGen
      (fun a b => ∃ i, ends i false = a ∧ ends i true = b) v w) :
    LinearMap.range (incidenceBoundary (K := K) ends) =
      LinearMap.ker vertexAugmentation := by
  apply le_antisymm (incidenceBoundary_range_le ends)
  intro c hc
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hc0 : ∑ v, c v = 0 := by
    simpa only [LinearMap.mem_ker, vertexAugmentation_apply] using hc
  have heq : c = ∑ v, c v • (Pi.single v 1 - Pi.single v₀ (1 : K)) := by
    rw [Finset.sum_congr rfl (fun v _ => smul_sub (c v) _ _), Finset.sum_sub_distrib,
      ← Finset.sum_smul, hc0, zero_smul, sub_zero]
    exact pi_eq_sum_univ' c
  rw [heq]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _
    (vertex_difference_mem_range ends (hconn v₀ v))

theorem incidence_cycle_rank [Nonempty V] (ends : I → Bool → V)
    (hconn : ∀ v w, Relation.EqvGen
      (fun a b => ∃ i, ends i false = a ∧ ends i true = b) v w) :
    Module.finrank K (LinearMap.ker (incidenceBoundary (K := K) ends)) +
      Fintype.card V = Fintype.card I + 1 := by
  have hsurj : Function.Surjective (vertexAugmentation (K := K) (V := V)) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    intro a
    exact ⟨Pi.single v a, by simp⟩
  have hsum := (vertexAugmentation (K := K) (V := V)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, CommSemiring.finrank_self,
    Module.finrank_pi] at hsum
  have hboundary := (incidenceBoundary (K := K) ends).finrank_range_add_finrank_ker
  rw [incidenceBoundary_range_eq_ker ends hconn, Module.finrank_pi] at hboundary
  omega

end PoincareConjecture.M76.CutGraph
