import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Simplex.Singular.SimplexHorn
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open scoped Topology

universe u

namespace Poincare.Topology

theorem stdSimplex_face_zero (n : Nat) (i : Fin (n + 2))
    (z : stdSimplex Real (Fin (n + 1))) :
    stdSimplex.map i.succAbove z i = 0 := by
  classical
  change FunOnFinite.linearMap Real Real i.succAbove z i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  have hf : Finset.univ.filter (fun k : Fin (n + 1) => i.succAbove k = i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact Fin.succAbove_ne i k (Finset.mem_filter.mp hk).2
  rw [hf, Finset.sum_empty]

theorem stdSimplex_face_succAbove (n : Nat) (i : Fin (n + 2))
    (z : stdSimplex Real (Fin (n + 1))) (k : Fin (n + 1)) :
    stdSimplex.map i.succAbove z (i.succAbove k) = z k := by
  classical
  change FunOnFinite.linearMap Real Real i.succAbove z (i.succAbove k) = z k
  rw [FunOnFinite.linearMap_apply_apply]
  have hf : Finset.univ.filter (fun l : Fin (n + 1) =>
      i.succAbove l = i.succAbove k) = {k} := by
    ext l
    constructor
    · intro hl
      exact Finset.mem_singleton.mpr
        (Fin.succAbove_right_injective (Finset.mem_filter.mp hl).2)
    · intro hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ l,
        congrArg i.succAbove (Finset.mem_singleton.mp hl)⟩
  rw [hf, Finset.sum_singleton]

theorem stdSimplex_face_range_iff (n : Nat) (i : Fin (n + 2))
    (y : stdSimplex Real (Fin (n + 2))) :
    (∃ z : stdSimplex Real (Fin (n + 1)), stdSimplex.map i.succAbove z = y) ↔
      y i = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact stdSimplex_face_zero n i z
  · intro hy
    have hzsum : Finset.univ.sum (fun k : Fin (n + 1) => y (i.succAbove k)) = 1 := by
      have h : Finset.univ.sum (fun j : Fin (n + 2) => y j) = 1 := y.property.2
      rw [Fin.sum_univ_succAbove (fun j => y j) i, hy, zero_add] at h
      exact h
    let z : stdSimplex Real (Fin (n + 1)) :=
      ⟨fun k => y (i.succAbove k), ⟨fun k => y.property.1 _, hzsum⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      exact (stdSimplex_face_zero n i z).trans hy.symm
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      exact stdSimplex_face_succAbove n i z k

theorem exists_stdSimplex_compatible_face_extension
    {X : Type u} [TopologicalSpace X] (n : Nat) (i : Fin (n + 2))
    (g : ∀ j : Fin (n + 2), j ≠ i → C(stdSimplex Real (Fin (n + 1)), X))
    (hg : ∀ (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i)
      (z w : stdSimplex Real (Fin (n + 1))),
      stdSimplex.map j.succAbove z = stdSimplex.map k.succAbove w →
      g j hj z = g k hk w) :
    ∃ f : C(stdSimplex Real (Fin (n + 2)), X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i) (z : stdSimplex Real (Fin (n + 1))),
        f (stdSimplex.map j.succAbove z) = g j hj z := by
  classical
  let J := {j : Fin (n + 2) // j ≠ i}
  let D := Σ _ : J, stdSimplex Real (Fin (n + 1))
  let H := {p : stdSimplex Real (Fin (n + 2)) //
    ∃ j : Fin (n + 2), j ≠ i ∧ p j = 0}
  let q : C(D, H) :=
    ⟨fun a => ⟨stdSimplex.map a.1.val.succAbove a.2,
      ⟨a.1.val, a.1.property, stdSimplex_face_zero n a.1.val a.2⟩⟩,
      continuous_sigma (fun j => (stdSimplex.continuous_map j.val.succAbove).subtype_mk _)⟩
  have hqsurj : Function.Surjective q := by
    intro y
    obtain ⟨j, hji, hj⟩ := y.property
    obtain ⟨z, hz⟩ := (stdSimplex_face_range_iff n j y.val).mpr hj
    refine ⟨⟨⟨j, hji⟩, z⟩, ?_⟩
    exact Subtype.ext hz
  have hq : _root_.Topology.IsQuotientMap q :=
    _root_.Topology.IsQuotientMap.of_surjective_continuous hqsurj q.continuous
  let G : C(D, X) :=
    ⟨fun a => g a.1.val a.1.property a.2,
      continuous_sigma (fun j => (g j.val j.property).continuous)⟩
  have hG : Function.FactorsThrough G q := by
    intro a b hab
    exact hg a.1.val b.1.val a.1.property b.1.property a.2 b.2
      (congrArg Subtype.val hab)
  let Gbar : C(H, X) := hq.lift G hG
  obtain ⟨f, hf⟩ := exists_stdSimplex_horn_extension n i Gbar
  refine ⟨f, ?_⟩
  intro j hj z
  let a : D := ⟨⟨j, hj⟩, z⟩
  calc
    f (stdSimplex.map j.succAbove z) = Gbar (q a) := hf (q a)
    _ = g j hj z := DFunLike.congr_fun (hq.lift_comp G hG) a

end Poincare.Topology
