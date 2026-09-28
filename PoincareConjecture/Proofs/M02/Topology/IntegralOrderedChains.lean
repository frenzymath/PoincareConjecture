import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic








set_option autoImplicit false

noncomputable section

open scoped BigOperators

universe u v w

namespace PoincareConjecture.Proofs.M02.Topology

abbrev integralOrderedChains (V : Type u) (k : Nat) :=
  (Fin k → V) →₀ Int

def integralOrderedBoundary (V : Type u) (k : Nat) :
    integralOrderedChains V (k + 1) →ₗ[Int] integralOrderedChains V k :=
  ∑ i : Fin (k + 1), ((-1 : Int) ^ i.val) •
    Finsupp.lmapDomain Int Int (fun v : Fin (k + 1) → V => v ∘ i.succAbove)

def integralOrderedCone {V : Type u} (k : Nat) (b : V) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1) :=
  Finsupp.lmapDomain Int Int
    (fun v : Fin k → V => Fin.cons (α := fun _ : Fin (k + 1) => V) b v)

def integralOrderedMap {V : Type u} {W : Type v} (k : Nat) (f : V → W) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains W k :=
  Finsupp.lmapDomain Int Int (fun v : Fin k → V => f ∘ v)

theorem integralOrderedBoundary_single {V : Type u} (k : Nat)
    (v : Fin (k + 1) → V) (a : Int) :
    integralOrderedBoundary V k (Finsupp.single v a) =
      ∑ i : Fin (k + 1), ((-1 : Int) ^ i.val) •
        Finsupp.single (v ∘ i.succAbove) a := by
  simp [integralOrderedBoundary, Finsupp.lmapDomain_apply]

theorem integralOrderedCone_single {V : Type u} (k : Nat) (b : V)
    (v : Fin k → V) (a : Int) :
    integralOrderedCone k b (Finsupp.single v a) =
      Finsupp.single (Fin.cons (α := fun _ : Fin (k + 1) => V) b v) a := by
  simp [integralOrderedCone, Finsupp.lmapDomain_apply]

theorem integralOrderedMap_single {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (v : Fin k → V) (a : Int) :
    integralOrderedMap k f (Finsupp.single v a) = Finsupp.single (f ∘ v) a := by
  simp [integralOrderedMap, Finsupp.lmapDomain_apply]

theorem integralOrderedBoundary_cone_zero {V : Type u} (b : V)
    (c : integralOrderedChains V 0) :
    integralOrderedBoundary V 0 (integralOrderedCone 0 b c) = c := by
  have h : (integralOrderedBoundary V 0).comp (integralOrderedCone 0 b) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedBoundary V 0 (integralOrderedCone 0 b (Finsupp.single v a)) =
      Finsupp.single v a
    rw [integralOrderedCone_single, integralOrderedBoundary_single, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    exact congrArg (fun t : Fin 0 → V => Finsupp.single t a) (Subsingleton.elim _ _)
  exact LinearMap.congr_fun h c

theorem integralOrderedBoundary_cone_succ {V : Type u} (k : Nat) (b : V)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V (k + 1) (integralOrderedCone (k + 1) b c) =
      c - integralOrderedCone k b (integralOrderedBoundary V k c) := by
  have h : (integralOrderedBoundary V (k + 1)).comp (integralOrderedCone (k + 1) b) =
      LinearMap.id - (integralOrderedCone k b).comp (integralOrderedBoundary V k) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedBoundary V (k + 1)
        (integralOrderedCone (k + 1) b (Finsupp.single v a)) =
      Finsupp.single v a - integralOrderedCone k b
        (integralOrderedBoundary V k (Finsupp.single v a))
    have hzero :
        Fin.cons (α := fun _ : Fin (k + 2) => V) b v ∘
          (0 : Fin (k + 2)).succAbove = v := by
      funext i
      rfl
    have hremove (i : Fin (k + 1)) : i.removeNth v = v ∘ i.succAbove := by
      funext j
      rfl
    rw [integralOrderedCone_single, integralOrderedBoundary_single,
      integralOrderedBoundary_single, map_sum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, hzero, Fin.val_succ, pow_succ,
      mul_neg, mul_one, neg_smul, map_smul, integralOrderedCone_single,
      Fin.cons_comp_succ_succAbove, hremove, ← Finset.sum_neg_distrib,
      sub_eq_add_neg]
  exact LinearMap.congr_fun h c

theorem integralOrderedBoundary_boundary {V : Type u} (k : Nat)
    (c : integralOrderedChains V (k + 2)) :
    integralOrderedBoundary V k (integralOrderedBoundary V (k + 1) c) = 0 := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 0).comp (integralOrderedBoundary V 1) = 0 := by
        apply Finsupp.lhom_ext
        intro v a
        change integralOrderedBoundary V 0
          (integralOrderedBoundary V 1 (Finsupp.single v a)) = 0
        have hv : Finsupp.single v a =
            integralOrderedCone 1 (v 0) (Finsupp.single (Fin.tail v) a) := by
          rw [integralOrderedCone_single, Fin.cons_self_tail]
        rw [hv, integralOrderedBoundary_cone_succ, map_sub,
          integralOrderedBoundary_cone_zero, sub_self]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 1)).comp
          (integralOrderedBoundary V (k + 2)) = 0 := by
        apply Finsupp.lhom_ext
        intro v a
        change integralOrderedBoundary V (k + 1)
          (integralOrderedBoundary V (k + 2) (Finsupp.single v a)) = 0
        have hv : Finsupp.single v a =
            integralOrderedCone (k + 2) (v 0) (Finsupp.single (Fin.tail v) a) := by
          rw [integralOrderedCone_single, Fin.cons_self_tail]
        rw [hv, integralOrderedBoundary_cone_succ, map_sub,
          integralOrderedBoundary_cone_succ, ih, map_zero, sub_zero, sub_self]
      exact LinearMap.congr_fun h c

theorem integralOrderedMap_boundary {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (c : integralOrderedChains V (k + 1)) :
    integralOrderedMap k f (integralOrderedBoundary V k c) =
      integralOrderedBoundary W k (integralOrderedMap (k + 1) f c) := by
  have h : (integralOrderedMap k f).comp (integralOrderedBoundary V k) =
      (integralOrderedBoundary W k).comp (integralOrderedMap (k + 1) f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k f (integralOrderedBoundary V k (Finsupp.single v a)) =
      integralOrderedBoundary W k (integralOrderedMap (k + 1) f (Finsupp.single v a))
    rw [integralOrderedBoundary_single, map_sum, integralOrderedMap_single,
      integralOrderedBoundary_single]
    simp only [map_smul, integralOrderedMap_single, Function.comp_assoc]
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_cone {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (b : V) (c : integralOrderedChains V k) :
    integralOrderedMap (k + 1) f (integralOrderedCone k b c) =
      integralOrderedCone k (f b) (integralOrderedMap k f c) := by
  have h : (integralOrderedMap (k + 1) f).comp (integralOrderedCone k b) =
      (integralOrderedCone k (f b)).comp (integralOrderedMap k f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap (k + 1) f (integralOrderedCone k b (Finsupp.single v a)) =
      integralOrderedCone k (f b) (integralOrderedMap k f (Finsupp.single v a))
    rw [integralOrderedCone_single, integralOrderedMap_single,
      integralOrderedMap_single, integralOrderedCone_single]
    apply congrArg (fun t : Fin (k + 1) → W => Finsupp.single t a)
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_comp {V : Type u} {W : Type v} {Z : Type w}
    (k : Nat) (f : V → W) (g : W → Z) (c : integralOrderedChains V k) :
    integralOrderedMap k g (integralOrderedMap k f c) =
      integralOrderedMap k (g ∘ f) c := by
  have h : (integralOrderedMap k g).comp (integralOrderedMap k f) =
      integralOrderedMap k (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k g (integralOrderedMap k f (Finsupp.single v a)) =
      integralOrderedMap k (g ∘ f) (Finsupp.single v a)
    rw [integralOrderedMap_single, integralOrderedMap_single, integralOrderedMap_single]
    rfl
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_id {V : Type u} (k : Nat)
    (c : integralOrderedChains V k) :
    integralOrderedMap k (id : V → V) c = c := by
  have h : integralOrderedMap k (id : V → V) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k id (Finsupp.single v a) = Finsupp.single v a
    rw [integralOrderedMap_single]
    rfl
  exact LinearMap.congr_fun h c

end PoincareConjecture.Proofs.M02.Topology
