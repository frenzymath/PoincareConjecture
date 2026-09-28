import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Set.UnionLift
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic










set_option autoImplicit false

open Set
open scoped Topology




theorem exists_continuous_periodic_concat {X : Type*} [TopologicalSpace X]
    {N : ℕ} (hN : 0 < N) {ell : ℝ} (hell : 0 < ell)
    (alpha : Fin N → ℝ → X) (hcont : ∀ j, ContinuousOn (alpha j) (Icc 0 ell))
    (hmatch : ∀ j, alpha j ell = alpha (finRotate N j) 0) :
    ∃ f : ℝ → X, Continuous f ∧ Function.Periodic f ((N : ℝ) * ell) ∧
      ∀ j : Fin N, ∀ s ∈ Icc 0 ell, f ((j.val : ℝ) * ell + s) = alpha j s := by
  classical
  cases N with
  | zero => omega
  | succ n =>
    let p : ℝ := (n + 1 : ℕ) * ell
    have hp : 0 < p := mul_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) hell
    let A : Fin (n + 1) → Set ℝ := fun j => Icc ((j.val : ℝ) * ell)
      ((j.val : ℝ) * ell + ell)
    have hcover : Icc 0 p ⊆ ⋃ j, A j := by
      intro x hx
      rcases lt_or_eq_of_le hx.2 with hxlt | rfl
      · have hxdiv : 0 ≤ x / ell := div_nonneg hx.1 hell.le
        have hj : Nat.floor (x / ell) < n + 1 :=
          (Nat.floor_lt hxdiv).mpr ((div_lt_iff₀ hell).mpr hxlt)
        refine mem_iUnion.mpr ⟨⟨Nat.floor (x / ell), hj⟩, ?_⟩
        change (Nat.floor (x / ell) : ℝ) * ell ≤ x ∧
          x ≤ (Nat.floor (x / ell) : ℝ) * ell + ell
        refine ⟨(le_div_iff₀ hell).mp (Nat.floor_le hxdiv), ?_⟩
        have h := (div_lt_iff₀ hell).mp (Nat.lt_floor_add_one (x / ell))
        nlinarith
      · refine mem_iUnion.mpr ⟨Fin.last n, ?_⟩
        change (n : ℝ) * ell ≤ p ∧ p ≤ (n : ℝ) * ell + ell
        dsimp [p]
        push_cast
        constructor <;> nlinarith
    have hordered (i j : Fin (n + 1)) (hij : i.val < j.val) (x : ℝ)
        (hi : x ∈ A i) (hj : x ∈ A j) :
        alpha i (x - (i.val : ℝ) * ell) = alpha j (x - (j.val : ℝ) * ell) := by
      have hcast : (j.val : ℝ) ≤ (i.val : ℝ) + 1 := by
        have hi' := hi.2
        have hj' := hj.1
        nlinarith
      have hnat : j.val ≤ i.val + 1 := by exact_mod_cast hcast
      have hnext : j.val = i.val + 1 := by omega
      have hnextR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hnext
      have hx : x = (j.val : ℝ) * ell := by
        have hi' := hi.2
        have hj' := hj.1
        nlinarith
      have hlast : i ≠ Fin.last n := by
        intro heq
        have hiN : i.val = n := congrArg Fin.val heq
        omega
      have hrotate : finRotate (n + 1) i = j :=
        Fin.ext ((coe_finRotate_of_ne_last hlast).trans hnext.symm)
      rw [show x - (i.val : ℝ) * ell = ell by nlinarith,
        show x - (j.val : ℝ) * ell = 0 by rw [hx]; ring,
        hmatch i, hrotate]
    have hcompat (i j : Fin (n + 1)) (x : ℝ) (hi : x ∈ A i) (hj : x ∈ A j) :
        alpha i (x - (i.val : ℝ) * ell) = alpha j (x - (j.val : ℝ) * ell) := by
      rcases lt_trichotomy i.val j.val with hij | hij | hij
      · exact hordered i j hij x hi hj
      · obtain rfl := Fin.ext hij
        rfl
      · exact (hordered j i hij x hj hi).symm
    let piece : (j : Fin (n + 1)) → A j → X :=
      fun j x => alpha j (x - (j.val : ℝ) * ell)
    let f : ℝ → X := fun x => if hx : x ∈ ⋃ j, A j then
      iUnionLift A piece hcompat (⋃ j, A j) Subset.rfl ⟨x, hx⟩ else alpha 0 0
    have hagree (j : Fin (n + 1)) (x : ℝ) (hx : x ∈ A j) :
        f x = alpha j (x - (j.val : ℝ) * ell) := by
      have hxU : x ∈ ⋃ j, A j := mem_iUnion.mpr ⟨j, hx⟩
      dsimp only [f]
      rw [dif_pos hxU]
      exact iUnionLift_of_mem ⟨x, hxU⟩ hx
    have hfc (j : Fin (n + 1)) : ContinuousOn f (A j) := by
      have hshift : MapsTo (fun x : ℝ => x - (j.val : ℝ) * ell) (A j) (Icc 0 ell) := by
        intro x hx
        have hx' : (j.val : ℝ) * ell ≤ x ∧ x ≤ (j.val : ℝ) * ell + ell := hx
        constructor <;> linarith [hx'.1, hx'.2]
      exact ((hcont j).comp (continuous_id.sub continuous_const).continuousOn hshift).congr
        (hagree j)
    have hf : ContinuousOn f (Icc 0 p) :=
      ((locallyFinite_of_finite A).continuousOn_iUnion (fun _ => isClosed_Icc) hfc).mono hcover
    have hzero : f 0 = alpha 0 0 := by
      simpa using hagree 0 0 (show (0 : ℝ) ∈ A 0 by simpa [A] using hell.le)
    have hlast : f p = alpha (Fin.last n) ell := by
      have hmem : p ∈ A (Fin.last n) := by
        change (n : ℝ) * ell ≤ p ∧ p ≤ (n : ℝ) * ell + ell
        dsimp [p]
        push_cast
        constructor <;> nlinarith
      have heq : p - (n : ℝ) * ell = ell := by dsimp [p]; push_cast; ring
      simpa only [Fin.val_last, heq] using hagree (Fin.last n) p hmem
    have hends : f 0 = f p := by
      rw [hzero, hlast, hmatch (Fin.last n), finRotate_last]
    let : Fact (0 < p) := ⟨hp⟩
    let F : ℝ → X := fun x => AddCircle.liftIco p 0 f (x : AddCircle p)
    have hF : Continuous F := (AddCircle.liftIco_zero_continuous hends hf).comp
      (AddCircle.continuous_mk' p)
    have hperiodic : Function.Periodic F p := fun x =>
      congrArg (AddCircle.liftIco p 0 f) (AddCircle.coe_add_period p x)
    have hFagree (x : ℝ) (hx : x ∈ Icc 0 p) : F x = f x := by
      rcases lt_or_eq_of_le hx.2 with hxp | rfl
      · exact AddCircle.liftIco_zero_coe_apply ⟨hx.1, hxp⟩
      · calc
          F p = F 0 := by simpa using hperiodic 0
          _ = f 0 := AddCircle.liftIco_zero_coe_apply ⟨le_rfl, hp⟩
          _ = f p := hends
    refine ⟨F, hF, hperiodic, fun j s hs => ?_⟩
    have hmem : (j.val : ℝ) * ell + s ∈ A j := by
      constructor <;> linarith [hs.1, hs.2]
    have hj : (j.val : ℝ) + 1 ≤ (n + 1 : ℕ) := by exact_mod_cast j.is_lt
    have hx : (j.val : ℝ) * ell + s ∈ Icc 0 p := by
      refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hell.le) hs.1, ?_⟩
      dsimp [p]
      nlinarith [hs.2]
    rw [hFagree _ hx, hagree j _ hmem]
    congr 1
    ring
