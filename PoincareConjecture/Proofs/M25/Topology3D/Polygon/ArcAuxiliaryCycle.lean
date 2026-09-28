import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimplePolygon
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Find











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D



theorem exists_first_orbit_exit_or_repeat {V : Type*} [Finite V]
    (f : V → V) (A : Set V) (x0 : V) (hx0 : x0 ∈ A) :
    ∃ N : ℕ, 0 < N ∧ (∀ t : ℕ, t < N → f^[t] x0 ∈ A) ∧
      Function.Injective (fun i : Fin N => f^[i.val] x0) ∧
      ((f^[N] x0 ∉ A ∧ Function.Injective (fun i : Fin (N + 1) => f^[i.val] x0)) ∨
        ∃ j : Fin N, f^[N] x0 = f^[j.val] x0) := by
  classical
  let v (t : ℕ) := f^[t] x0
  let B (t : ℕ) := v t ∉ A ∨ ∃ s : ℕ, s < t ∧ v t = v s
  have hex : ∃ t, B t := by
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite v
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨j, Or.inr ⟨i, hlt, heq.symm⟩⟩
    · exact ⟨i, Or.inr ⟨j, hlt, heq⟩⟩
  let N := Nat.find hex
  have hevent : B N := Nat.find_spec hex
  have hnot (t : ℕ) (ht : t < N) : ¬ B t := Nat.find_min hex ht
  have hzero : ¬ B 0 := by simp [B, v, hx0]
  have hN : 0 < N := Nat.pos_of_ne_zero (fun h => hzero (h ▸ hevent))
  have hact (t : ℕ) (ht : t < N) : v t ∈ A := by
    by_contra h
    exact hnot t ht (Or.inl h)
  have hinj : Function.Injective (fun i : Fin N => v i.val) := by
    intro i j heq
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt | he | hlt
    · exact (hnot j.val j.isLt (Or.inr ⟨i.val, hlt, heq.symm⟩)).elim
    · exact he
    · exact (hnot i.val i.isLt (Or.inr ⟨j.val, hlt, heq⟩)).elim
  refine ⟨N, hN, hact, hinj, ?_⟩
  rcases hevent with hout | ⟨j, hj, heq⟩
  · left
    refine ⟨hout, ?_⟩
    intro i j heq
    change v i.val = v j.val at heq
    apply Fin.ext
    by_cases hi : i.val < N
    · by_cases hj : j.val < N
      · exact congrArg (fun k : Fin N => k.val)
          (hinj (a₁ := ⟨i.val, hi⟩) (a₂ := ⟨j.val, hj⟩) heq)
      · have hjN : j.val = N := by omega
        exact (hout (hjN ▸ heq ▸ hact i.val hi)).elim
    · have hiN : i.val = N := by omega
      by_cases hj : j.val < N
      · exact (hout (hiN ▸ heq.symm ▸ hact j.val hj)).elim
      · omega
  · exact Or.inr ⟨⟨j, hj⟩, heq⟩




theorem exists_simplePolygon_of_first_orbit_repeat {V E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : V → V) (A : Set V) (x0 : V) (e : V → E) (G : Set E)
    (he : Function.Injective e) (heG : ∀ u : V, e u ∈ G)
    (h1 : ∀ u ∈ A, f u ≠ u)
    (h2 : ∀ u ∈ A, f u ∈ A → f (f u) ≠ u)
    (hvis : ∀ u ∈ A, Disjoint (openSegment ℝ (e u) (e (f u))) G)
    (hinc : ∀ u ∈ A, ∀ w ∈ A, u ≠ w →
      segment ℝ (e u) (e (f u)) ∩ segment ℝ (e w) (e (f w)) =
        {e u, e (f u)} ∩ {e w, e (f w)})
    (N j : ℕ) (hj : j < N) (hact : ∀ t : ℕ, t < N → f^[t] x0 ∈ A)
    (hinj : Function.Injective (fun i : Fin N => f^[i.val] x0))
    (hclose : f^[N] x0 = f^[j] x0) :
    3 ≤ N - j ∧ ∃ r : Polygon E (N - j),
      (∀ i : Fin (N - j), r i = e (f^[j + i.val] x0)) ∧ IsSimplePolygon r ∧
      (∀ i : Fin (N - j), f^[j + i.val] x0 ∈ A ∧
        f^[j + (finRotate (N - j) i).val] x0 = f (f^[j + i.val] x0)) ∧
      (∀ i : Fin (N - j), r.edgeSet ℝ i =
        segment ℝ (e (f^[j + i.val] x0)) (e (f (f^[j + i.val] x0)))) ∧
      r.boundary ℝ ∩ G = range r := by
  let v (t : ℕ) := f^[t] x0
  have hstep (t : ℕ) : v (t + 1) = f (v t) := Function.iterate_succ_apply' f t x0
  have hthree : 3 ≤ N - j := by
    by_contra h
    have hcases : N = j + 1 ∨ N = j + 2 := by omega
    rcases hcases with hN | hN
    · apply h1 (v j) (hact j hj)
      rw [← hstep, ← hN]
      exact hclose
    · have hja : v (j + 1) ∈ A := hact _ (by omega)
      apply h2 (v j) (hact j hj) (hstep j ▸ hja)
      rw [← hstep, ← hstep, ← hN]
      exact hclose
  let c (i : Fin (N - j)) := v (j + i.val)
  have hbound (i : Fin (N - j)) : j + i.val < N := by have := i.isLt; omega
  have hcA (i : Fin (N - j)) : c i ∈ A := hact _ (hbound i)
  have hcinj : Function.Injective c := by
    intro i k heq
    have hh := congrArg Fin.val
      (hinj (a₁ := ⟨j + i.val, hbound i⟩) (a₂ := ⟨j + k.val, hbound k⟩) heq)
    apply Fin.ext
    dsimp only at hh
    omega
  have hrotate (L : ℕ) (hL : N - j = L) (i : Fin L) :
      v (j + (finRotate L i).val) = f (v (j + i.val)) := by
    cases L with
    | zero => exact Fin.elim0 i
    | succ m =>
      by_cases hi : i = Fin.last m
      · subst i
        rw [finRotate_last]
        simp only [Fin.val_zero, Fin.val_last, Nat.add_zero]
        rw [← hstep, show j + m + 1 = N from by omega]
        exact hclose.symm
      · rw [coe_finRotate_of_ne_last hi, ← Nat.add_assoc, hstep]
  have hnext (i : Fin (N - j)) : c (finRotate (N - j) i) = f (c i) :=
    hrotate _ rfl i
  let r : Polygon E (N - j) := Polygon.mk (fun i => e (c i))
  have hr (i : Fin (N - j)) : r i = e (c i) := rfl
  have hedge (i : Fin (N - j)) :
      r.edgeSet ℝ i = segment ℝ (e (c i)) (e (f (c i))) := by
    rw [polygon_edgeSet_eq_segment, hr, hr, hnext]
  have hsimple : IsSimplePolygon r := by
    refine ⟨hthree, he.comp hcinj, ?_⟩
    intro i k hik
    rw [hedge, hedge]
    simpa only [hr, hnext] using
      (hinc (c i) (hcA i) (c k) (hcA k) (fun h => hik (hcinj h))).le
  have hcontact : r.boundary ℝ ∩ G = range r := by
    apply subset_antisymm
    · rintro x ⟨hxB, hxG⟩
      obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff r x).mp hxB
      rw [hedge, ← insert_endpoints_openSegment] at hi
      rcases hi with rfl | rfl | hi
      · exact ⟨i, rfl⟩
      · refine ⟨finRotate (N - j) i, ?_⟩
        rw [hr, hnext]
      · exact (Set.disjoint_left.mp (hvis (c i) (hcA i)) hi hxG).elim
    · rintro x ⟨i, rfl⟩
      exact ⟨polygon_vertex_mem_boundary r i, heG (c i)⟩
  exact ⟨hthree, r, hr, hsimple, fun i => ⟨hcA i, hnext i⟩, hedge, hcontact⟩

end PoincareConjecture.M25.Topology3D
