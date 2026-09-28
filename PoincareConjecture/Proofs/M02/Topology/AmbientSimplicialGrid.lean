import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M02.Topology

variable {N : Nat}

noncomputable def ambientGridPoint (h : Real) (z : Fin N → Int) :
    EuclideanSpace Real (Fin N) :=
  (EuclideanSpace.equiv (Fin N) Real).symm (fun i => h * (z i : Real))

noncomputable def ambientGridCorner (h : Real) (z : Fin N → Int)
    (pi : Equiv.Perm (Fin N)) (k : Fin (N + 1)) :
    EuclideanSpace Real (Fin N) :=
  ambientGridPoint h (fun i => z i + if (pi.symm i).val < k.val then 1 else 0)

noncomputable def ambientGridSimplex (h : Real) (z : Fin N → Int)
    (pi : Equiv.Perm (Fin N)) : Finset (EuclideanSpace Real (Fin N)) :=
  Finset.univ.image (ambientGridCorner h z pi)

def ambientGridFaces (h : Real) (B : Nat) :
    Set (Finset (EuclideanSpace Real (Fin N))) :=
  {s | s.Nonempty ∧ ∃ (z : Fin N → Int) (pi : Equiv.Perm (Fin N)),
    (∀ i, -(B : Int) ≤ z i ∧ z i < (B : Int)) ∧ s ⊆ ambientGridSimplex h z pi}

def ambientGridStarBound (N : Nat) : Nat :=
  2 ^ (2 * N + 2) * (Nat.factorial N + 1)

set_option maxHeartbeats 4000000 in

theorem ambient_grid_simplex_geometry (h : Real) (hh : 0 < h)
    (z : Fin N → Int) (pi : Equiv.Perm (Fin N))
    (s : Finset (EuclideanSpace Real (Fin N))) (hs : s.Nonempty)
    (hsub : s ⊆ ambientGridSimplex h z pi) :
    AffineIndependent Real ((↑) : s → EuclideanSpace Real (Fin N)) ∧
    s.card ≤ N + 1 ∧
    Metric.diam (convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ≤
      (N + 1 : Real) * h ∧
    (2 ≤ s.card → ∀ v ∈ s,
      h / 2 ≤ Metric.infDist v
        (affineSpan Real ((s.erase v : Finset (EuclideanSpace Real (Fin N))) :
          Set (EuclideanSpace Real (Fin N))) : Set (EuclideanSpace Real (Fin N)))) := by
  classical
  have _ := hs
  let E := EuclideanSpace Real (Fin N)
  let c := ambientGridCorner h z pi
  have hc (k : Fin (N + 1)) (i : Fin N) :
      c k i = h * ((z i : Real) + if (pi.symm i).val < k.val then 1 else 0) := by
    change h * ((z i + if (pi.symm i).val < k.val then 1 else 0 : Int) : Real) = _
    split_ifs <;> simp
  let b (i : Fin N) : E →ᵃ[Real] Real :=
    (EuclideanSpace.projₗ (pi i)).toAffineMap - AffineMap.const Real E (h * (z (pi i) : Real))
  let L (k : Fin (N + 1)) : E →ᵃ[Real] Real :=
    (if hk : 0 < k.val then b ⟨k.val - 1, by omega⟩ else AffineMap.const Real E h) -
      (if hk : k.val < N then b ⟨k.val, hk⟩ else 0)
  have hbval (i : Fin N) (j : Fin (N + 1)) :
      b i (c j) = if i.val < j.val then h else 0 := by
    change c j (pi i) - h * (z (pi i) : Real) = _
    rw [hc]
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> ring
  have hcoeff (k j : Fin (N + 1)) :
      (if 0 < k.val then (if k.val - 1 < j.val then h else 0) else h) -
        (if k.val < N then (if k.val < j.val then h else 0) else 0) =
          if k = j then h else 0 := by
    by_cases hkj : k = j
    · subst j
      by_cases hk : 0 < k.val
      · have hpred : k.val - 1 < k.val := by omega
        simp only [if_pos hk, if_pos hpred, lt_self_iff_false, if_false, ite_self,
          if_true, sub_zero]
      · simp only [if_neg hk, lt_self_iff_false, if_false, ite_self,
          if_true, sub_zero]
    · have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he)
      split_ifs <;> simp_all only [sub_zero, sub_self] <;> omega
  have hL (k j : Fin (N + 1)) : L k (c j) = if k = j then h else 0 := by
    by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
    · simpa only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
        hbval, Fin.val_mk, if_pos hp, if_pos hn] using hcoeff k j
    · simpa only [L, dif_pos hp, dif_neg hn, sub_zero, hbval, Fin.val_mk,
        if_pos hp, if_neg hn] using hcoeff k j
    · simpa only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
        AffineMap.const_apply, hbval, Fin.val_mk, if_neg hp, if_pos hn] using hcoeff k j
    · simpa only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply,
        if_neg hp, if_neg hn] using hcoeff k j
  have hind : AffineIndependent Real c := by
    rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
    intro w w' hw hw' heq
    funext k
    have he := congrArg (L k) heq
    rw [Finset.univ.map_affineCombination c w hw (L k),
      Finset.univ.map_affineCombination c w' hw' (L k),
      Finset.affineCombination_eq_linear_combination _ _ _ hw,
      Finset.affineCombination_eq_linear_combination _ _ _ hw'] at he
    simp only [Function.comp_apply, hL, smul_eq_mul, mul_ite, mul_zero] at he
    simpa [Finset.sum_ite_eq', hh.ne'] using he
  have hsrange : (s : Set E) ⊆ Set.range c := by
    intro x hx
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hsub hx)
    exact ⟨k, hk⟩
  refine ⟨hind.range.mono hsrange, ?_, ?_, ?_⟩
  · exact (Finset.card_le_card hsub).trans
      ((Finset.card_image_le).trans (by simp))
  · rw [convexHull_diam]
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    intro x hx y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hsub hx)
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (hsub hy)
    have hsq : ‖c j - c k‖ ^ 2 ≤ (N : Real) * h ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        ∑ i, ((c j - c k) i) ^ 2 ≤ ∑ _i : Fin N, h ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          change (c j i - c k i) ^ 2 ≤ h ^ 2
          rw [hc, hc]
          split_ifs <;> nlinarith [sq_nonneg h]
        _ = (N : Real) * h ^ 2 := by simp
    have hn : (0 : Real) ≤ N := Nat.cast_nonneg N
    change ‖c j - c k‖ ≤ (N + 1 : Real) * h
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (N + 1 : Real) * h)).1
    calc
      ‖c j - c k‖ ^ 2 ≤ (N : Real) * h ^ 2 := hsq
      _ ≤ (N + 1 : Real) ^ 2 * h ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg h)
      _ = ((N + 1 : Real) * h) ^ 2 := by ring
  · intro hcard v hv
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hsub hv)
    have hdist (x y : E) : |L k x - L k y| ≤ 2 * dist x y := by
      have hb (i : Fin N) : |b i x - b i y| ≤ dist x y := by
        change |(x (pi i) - h * (z (pi i) : Real)) -
          (y (pi i) - h * (z (pi i) : Real))| ≤ dist x y
        simpa only [sub_sub_sub_cancel_right, Real.dist_eq] using
          (PiLp.dist_apply_le x y (pi i))
      by_cases hp : 0 < k.val <;> by_cases hn : k.val < N
      · simp only [L, dif_pos hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply]
        change |(b ⟨k.val - 1, _⟩ x - b ⟨k.val, _⟩ x) -
          (b ⟨k.val - 1, _⟩ y - b ⟨k.val, _⟩ y)| ≤ _
        rw [show (b ⟨k.val - 1, _⟩ x - b ⟨k.val, _⟩ x) -
            (b ⟨k.val - 1, _⟩ y - b ⟨k.val, _⟩ y) =
            (b ⟨k.val - 1, _⟩ x - b ⟨k.val - 1, _⟩ y) -
              (b ⟨k.val, _⟩ x - b ⟨k.val, _⟩ y) by ring]
        exact (abs_sub _ _).trans (by linarith [hb ⟨k.val - 1, by omega⟩, hb ⟨k.val, hn⟩])
      · simp only [L, dif_pos hp, dif_neg hn, sub_zero]
        exact (hb ⟨k.val - 1, by omega⟩).trans
          (by linarith [show 0 ≤ dist x y from dist_nonneg])
      · simp only [L, dif_neg hp, dif_pos hn, AffineMap.coe_sub, Pi.sub_apply,
          AffineMap.const_apply]
        rw [sub_sub_sub_cancel_left, abs_sub_comm]
        exact (hb ⟨k.val, hn⟩).trans
          (by linarith [show 0 ≤ dist x y from dist_nonneg])
      · simp only [L, dif_neg hp, dif_neg hn, sub_zero, AffineMap.const_apply,
          sub_self, abs_zero]
        positivity
    have hzero : ∀ x ∈ affineSpan Real ((s.erase v : Finset E) : Set E), L k x = 0 := by
      intro x hx
      refine affineSpan_induction hx ?_ ?_
      · intro x hx
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub (Finset.mem_erase.mp hx).2)
        have hjk : k ≠ j := by
          intro hkj
          apply (Finset.mem_erase.mp hx).1
          rw [← hj, ← hkj, hk]
        rw [← hj, hL, if_neg hjk]
      · intro a x y w hx hy hw
        rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
        simp [hx, hy, hw]
    have hne : (s.erase v).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
      omega
    obtain ⟨w, hw⟩ := hne
    apply (Metric.le_infDist ⟨w, subset_affineSpan Real _ hw⟩).2
    intro x hx
    have hd := hdist v x
    have hvL : L k v = h := by rw [← hk, hL, if_pos rfl]
    rw [hvL, hzero x hx, sub_zero, abs_of_pos hh] at hd
    linarith

set_option maxHeartbeats 4000000 in

theorem ambient_grid_star_count (h : Real) (hh : 0 < h)
    (v : EuclideanSpace Real (Fin N)) :
    Set.Finite {s : Finset (EuclideanSpace Real (Fin N)) |
      s.Nonempty ∧ v ∈ s ∧ ∃ z pi, s ⊆ ambientGridSimplex h z pi} ∧
    Set.ncard {s : Finset (EuclideanSpace Real (Fin N)) |
      s.Nonempty ∧ v ∈ s ∧ ∃ z pi, s ⊆ ambientGridSimplex h z pi} ≤
        ambientGridStarBound N := by
  classical
  let S := {s : Finset (EuclideanSpace Real (Fin N)) |
    s.Nonempty ∧ v ∈ s ∧ ∃ z pi, s ⊆ ambientGridSimplex h z pi}
  change S.Finite ∧ S.ncard ≤ ambientGridStarBound N
  by_cases hempty : S = ∅
  · simp only [hempty, Set.finite_empty, Set.ncard_empty, Nat.zero_le, and_self]
  obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨z, pi, hsub⟩ := hs.2.2
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hsub hs.2.1)
  let a : Fin N → Int := fun i => z i + if (pi.symm i).val < k.val then 1 else 0
  have hva : v = ambientGridPoint h a := hk.symm
  let Z : Finset (Fin N → Int) := Fintype.piFinset (fun i => {a i - 1, a i})
  let Q : Finset (Finset (EuclideanSpace Real (Fin N))) :=
    Z.biUnion fun z => Finset.univ.biUnion fun pi : Equiv.Perm (Fin N) =>
      (ambientGridSimplex h z pi).powerset
  have hSQ : S ⊆ Q := by
    intro t ht
    obtain ⟨z', pi', hsub'⟩ := ht.2.2
    obtain ⟨k', _, hk'⟩ := Finset.mem_image.mp (hsub' ht.2.1)
    have hz' : z' ∈ Z := by
      rw [Fintype.mem_piFinset]
      intro i
      have he := congrArg (fun x : EuclideanSpace Real (Fin N) => x i) (hk'.trans hva)
      change h * ((z' i + if (pi'.symm i).val < k'.val then 1 else 0 : Int) : Real) =
        h * (a i : Real) at he
      have hi := mul_left_cancel₀ hh.ne' he
      have hi' : z' i + (if (pi'.symm i).val < k'.val then 1 else 0) = a i := by
        exact_mod_cast hi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      split_ifs at hi' <;> omega
    exact Finset.mem_biUnion.mpr ⟨z', hz',
      Finset.mem_biUnion.mpr ⟨pi', Finset.mem_univ _, Finset.mem_powerset.mpr hsub'⟩⟩
  have hZ : Z.card = 2 ^ N := by
    simp [Z, Fintype.card_piFinset, show ∀ i : Fin N, a i - 1 ≠ a i by intro i; omega]
  have hQ : Q.card ≤ 2 ^ N * Nat.factorial N * 2 ^ (N + 1) := by
    calc
      Q.card ≤ ∑ z' ∈ Z, (Finset.univ.biUnion fun pi' : Equiv.Perm (Fin N) =>
          (ambientGridSimplex h z' pi').powerset).card := Finset.card_biUnion_le
      _ ≤ ∑ _z' ∈ Z, ∑ _pi' : Equiv.Perm (Fin N), 2 ^ (N + 1) := by
        apply Finset.sum_le_sum
        intro z' _
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
        intro pi' _
        rw [Finset.card_powerset]
        apply Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
        exact (Finset.card_image_le).trans (by simp)
      _ = 2 ^ N * Nat.factorial N * 2 ^ (N + 1) := by
        simp [hZ, Fintype.card_perm, Nat.mul_assoc]
  refine ⟨Q.finite_toSet.subset hSQ, (Set.ncard_le_ncard hSQ Q.finite_toSet).trans ?_⟩
  rw [Set.ncard_coe_finset]
  refine hQ.trans ?_
  have hp : 2 ^ N * 2 ^ (N + 1) = 2 ^ (2 * N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hp' : 2 ^ (2 * N + 2) = 2 ^ (2 * N + 1) * 2 := by
    rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega, pow_succ]
  dsimp only [ambientGridStarBound]
  rw [mul_right_comm, hp, hp']
  nlinarith [Nat.zero_le (2 ^ (2 * N + 1))]

set_option maxHeartbeats 4000000 in

theorem ambient_grid_faces_locally_finite (h : Real) (hh : 0 < h)
    (c : EuclideanSpace Real (Fin N)) (R : Real) :
    Set.Finite {q : (Fin N → Int) × Equiv.Perm (Fin N) |
      (convexHull Real (ambientGridSimplex h q.1 q.2 :
        Set (EuclideanSpace Real (Fin N))) ∩ Metric.closedBall c R).Nonempty} := by
  classical
  let Z : Finset (Fin N → Int) := Fintype.piFinset (fun i =>
    Finset.Icc (⌊(c i - R) / h⌋ - 1) ⌈(c i + R) / h⌉)
  apply (Z.finite_toSet.prod (Set.finite_univ :
    (Set.univ : Set (Equiv.Perm (Fin N))).Finite)).subset
  rintro ⟨z, pi⟩ ⟨x, hx, hball⟩
  refine ⟨?_, Set.mem_univ _⟩
  change z ∈ Fintype.piFinset _
  rw [Fintype.mem_piFinset]
  intro i
  have hbox : h * (z i : Real) ≤ x i ∧ x i ≤ h * ((z i : Real) + 1) := by
    apply convexHull_min (t := (EuclideanSpace.projₗ i) ⁻¹'
      Set.Icc (h * (z i : Real)) (h * ((z i : Real) + 1))) ?_
      ((convex_Icc _ _).linear_preimage (EuclideanSpace.projₗ i)) hx
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    change h * (z i : Real) ≤
        h * ((z i + if (pi.symm i).val < k.val then 1 else 0 : Int) : Real) ∧
      h * ((z i + if (pi.symm i).val < k.val then 1 else 0 : Int) : Real) ≤
        h * ((z i : Real) + 1)
    split_ifs <;> push_cast <;> constructor <;> nlinarith
  have hd : |x i - c i| ≤ R := by
    exact (show |x i - c i| ≤ dist x c by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le x c i).trans hball
  have hl : ((⌊(c i - R) / h⌋ - 1 : Int) : Real) ≤ (z i : Real) := by
    have hf := Int.floor_le ((c i - R) / h)
    have hb : (c i - R) / h ≤ (z i : Real) + 1 :=
      (div_le_iff₀ hh).2 (by nlinarith [(abs_le.mp hd).1])
    push_cast
    linarith
  have hu : (z i : Real) ≤ (⌈(c i + R) / h⌉ : Int) := by
    have hf := Int.le_ceil ((c i + R) / h)
    have hb : (z i : Real) ≤ (c i + R) / h :=
      (le_div_iff₀ hh).2 (by nlinarith [(abs_le.mp hd).2])
    exact hb.trans hf
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

set_option maxHeartbeats 4000000 in

theorem exists_ambient_grid_complex (h : Real) (hh : 0 < h)
    (B : Nat) (hB : 0 < B) :
    ∃ K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N)),
      K.faces = ambientGridFaces h B ∧ Set.Finite K.faces ∧
      K.space = {x | ∀ i : Fin N, -(B : Real) * h ≤ x i ∧ x i ≤ (B : Real) * h} := by
  classical
  let E := EuclideanSpace Real (Fin N)
  have hc (z : Fin N → Int) (pi : Equiv.Perm (Fin N))
      (k : Fin (N + 1)) (i : Fin N) :
      ambientGridCorner h z pi k i =
        h * ((z i : Real) + if (pi.symm i).val < k.val then 1 else 0) := by
    change h * ((z i + if (pi.symm i).val < k.val then 1 else 0 : Int) : Real) = _
    split_ifs <;> simp
  have hinj (z : Fin N → Int) (pi : Equiv.Perm (Fin N)) :
      Function.Injective (ambientGridCorner h z pi) := by
    have hlt (k l : Fin (N + 1)) (hkl : k.val < l.val) :
        ambientGridCorner h z pi k ≠ ambientGridCorner h z pi l := by
      intro heq
      let i : Fin N := ⟨k.val, by omega⟩
      have hi := congrArg (fun x : E => x (pi i)) heq
      rw [hc, hc] at hi
      simp only [Equiv.symm_apply_apply, i, lt_self_iff_false, if_false,
        if_pos hkl] at hi
      nlinarith
    intro k l heq
    apply Fin.ext
    rcases lt_trichotomy k.val l.val with hkl | hkl | hkl
    · exact False.elim (hlt k l hkl heq)
    · exact hkl
    · exact False.elim (hlt l k hkl heq.symm)
  have hbox (z : Fin N → Int) (pi : Equiv.Perm (Fin N)) (x : E)
      (hx : x ∈ convexHull Real (ambientGridSimplex h z pi : Set E)) (i : Fin N) :
      h * (z i : Real) ≤ x i ∧ x i ≤ h * ((z i : Real) + 1) := by
    apply convexHull_min (t := (EuclideanSpace.projₗ i) ⁻¹'
      Set.Icc (h * (z i : Real)) (h * ((z i : Real) + 1))) ?_
      ((convex_Icc _ _).linear_preimage (EuclideanSpace.projₗ i)) hx
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    change h * (z i : Real) ≤ ambientGridCorner h z pi k i ∧
      ambientGridCorner h z pi k i ≤ h * ((z i : Real) + 1)
    rw [hc]
    split_ifs <;> constructor <;> linarith
  have hmean (z : Fin N → Int) (pi : Equiv.Perm (Fin N))
      (w : Fin (N + 1) → Real) (hw : ∑ k, w k = 1) (i : Fin N) :
      (∑ k, w k • ambientGridCorner h z pi k) i =
        h * ((z i : Real) + ∑ k, if (pi.symm i).val < k.val then w k else 0) := by
    change (EuclideanSpace.projₗ i) (∑ k, w k • ambientGridCorner h z pi k) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      ∑ k, w k * ambientGridCorner h z pi k i =
          ∑ k, (h * (z i : Real) * w k +
            h * (if (pi.symm i).val < k.val then w k else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hc]
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw]; ring
  have hweights (z : Fin N → Int) (pi : Equiv.Perm (Fin N))
      (s : Finset E) (hsub : s ⊆ ambientGridSimplex h z pi) (x : E)
      (hx : x ∈ convexHull Real (s : Set E)) :
      ∃ w : Fin (N + 1) → Real, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
        (∑ k, w k • ambientGridCorner h z pi k) = x ∧
        ∀ k, 0 < w k → ambientGridCorner h z pi k ∈ s := by
    obtain ⟨a, ha, ha1, hax⟩ := Finset.mem_convexHull'.mp hx
    let w k := if ambientGridCorner h z pi k ∈ s then a (ambientGridCorner h z pi k) else 0
    have hf : (ambientGridSimplex h z pi).filter (fun v => v ∈ s) = s := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hv => ⟨hsub hv, hv⟩⟩
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only [w]
      split_ifs with hk
      · exact ha _ hk
      · exact le_rfl
    · change ∑ k, (if ambientGridCorner h z pi k ∈ s then
        a (ambientGridCorner h z pi k) else 0) = 1
      rw [← Finset.sum_image (s := Finset.univ) (g := ambientGridCorner h z pi)
        (f := fun v : E => if v ∈ s then a v else 0) (hinj z pi).injOn,
        ← Finset.sum_filter]
      change ∑ v ∈ (ambientGridSimplex h z pi).filter (fun v => v ∈ s), a v = 1
      rw [hf]
      exact ha1
    · change (∑ k, (if ambientGridCorner h z pi k ∈ s then
        a (ambientGridCorner h z pi k) else 0) • ambientGridCorner h z pi k) = x
      simp only [ite_smul, zero_smul]
      rw [← Finset.sum_image (s := Finset.univ) (g := ambientGridCorner h z pi)
        (f := fun v : E => if v ∈ s then a v • v else 0) (hinj z pi).injOn,
        ← Finset.sum_filter]
      change (∑ v ∈ (ambientGridSimplex h z pi).filter (fun v => v ∈ s), a v • v) = x
      rw [hf]
      exact hax
    · intro k hk
      by_contra hn
      simp [w, hn] at hk

  have hround (z : Fin N → Int) (pi : Equiv.Perm (Fin N))
      (w : Fin (N + 1) → Real) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
      (x : E) (hwx : ∑ k, w k • ambientGridCorner h z pi k = x)
      (k : Fin (N + 1)) (t : Real) (ht0 : 0 < t) (ht1 : t < 1)
      (ha : (∑ l, if k < l then w l else 0) ≤ t)
      (hb : t < ∑ l, if k ≤ l then w l else 0) :
      ambientGridCorner h z pi k = ambientGridPoint h (fun i => ⌈x i / h - t⌉) := by
    ext i
    let p : Real := ∑ l, if (pi.symm i).val < l.val then w l else 0
    have hp0 : 0 ≤ p := Finset.sum_nonneg fun l _ => by
      split_ifs
      · exact hw0 l
      · exact le_rfl
    have hp1 : p ≤ 1 := by
      rw [← hw1]
      exact Finset.sum_le_sum fun l _ => by split_ifs <;> simp [hw0]
    have hxp : x i / h = (z i : Real) + p := by
      have hm := hmean z pi w hw1 i
      rw [hwx] at hm
      apply (div_eq_iff hh.ne').2
      dsimp only [p]
      nlinarith [hm]
    by_cases hik : (pi.symm i).val < k.val
    · have hpt : t < p := hb.trans_le (Finset.sum_le_sum fun l _ => by
        split_ifs <;> try exact le_rfl
        · omega
        · exact hw0 l)
      have hz : ⌈x i / h - t⌉ = z i + 1 := by
        apply Int.ceil_eq_iff.mpr
        rw [hxp]
        push_cast
        constructor <;> linarith
      change ambientGridCorner h z pi k i = h * (⌈x i / h - t⌉ : Int)
      rw [hc, if_pos hik, hz]
      push_cast
      rfl
    · have hpt : p ≤ t := (Finset.sum_le_sum fun l _ => by
        split_ifs <;> try exact le_rfl
        · omega
        · exact hw0 l).trans ha
      have hz : ⌈x i / h - t⌉ = z i := by
        apply Int.ceil_eq_iff.mpr
        rw [hxp]
        constructor <;> linarith
      change ambientGridCorner h z pi k i = h * (⌈x i / h - t⌉ : Int)
      rw [hc, if_neg hik, hz, add_zero]
  have hthreshold (w : Fin (N + 1) → Real) (hw0 : ∀ k, 0 ≤ w k)
      (hw1 : ∑ k, w k = 1) (t : Real) (ht0 : 0 < t) (ht1 : t < 1) :
      ∃ k : Fin (N + 1), 0 < w k ∧
        (∑ l, if k < l then w l else 0) ≤ t ∧ t < ∑ l, if k ≤ l then w l else 0 := by
    let Q := Finset.univ.filter (fun k : Fin (N + 1) => t < ∑ l, if k ≤ l then w l else 0)
    have hQ : Q.Nonempty := ⟨0, by simp [Q, hw1, ht1]⟩
    let k := Q.max' hQ
    have hk : k ∈ Q := Finset.max'_mem Q hQ
    have hb : t < ∑ l, if k ≤ l then w l else 0 := (Finset.mem_filter.mp hk).2
    have ha : (∑ l, if k < l then w l else 0) ≤ t := by
      by_cases hkN : k.val < N
      · let k' : Fin (N + 1) := ⟨k.val + 1, by omega⟩
        have hn : k' ∉ Q := by
          intro hq
          have hm := Finset.le_max' Q k' hq
          change k'.val ≤ k.val at hm
          dsimp [k'] at hm
          omega
        have ht : (∑ l, if k' ≤ l then w l else 0) ≤ t := by
          simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hn
        convert ht using 1
        apply Finset.sum_congr rfl
        intro l _
        have he : k < l ↔ k' ≤ l := by change k.val < l.val ↔ k.val + 1 ≤ l.val; omega
        simp only [he]
      · have he : ∀ l : Fin (N + 1), ¬k < l := by intro l; change ¬k.val < l.val; omega
        simp only [he, if_false, Finset.sum_const_zero]
        exact ht0.le
    have hsplit : (∑ l, if k ≤ l then w l else 0) =
        w k + ∑ l, if k < l then w l else 0 := by
      calc
        _ = ∑ l, ((if l = k then w k else 0) + if k < l then w l else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          split_ifs <;> simp_all <;> omega
        _ = _ := by simp [Finset.sum_add_distrib]
    exact ⟨k, by linarith, ha, hb⟩
  have hinter (s t : Finset E) (hs : s ∈ ambientGridFaces h B)
      (ht : t ∈ ambientGridFaces h B) :
      convexHull Real (s : Set E) ∩ convexHull Real (t : Set E) ⊆
        convexHull Real (s ∩ t : Set E) := by
    obtain ⟨_, z, pi, _, hsub⟩ := hs
    obtain ⟨_, z', pi', _, hsub'⟩ := ht
    rintro x ⟨hxs, hxt⟩
    obtain ⟨w, hw0, hw1, hwx, hws⟩ := hweights z pi s hsub x hxs
    obtain ⟨w', hw0', hw1', hwx', hwt⟩ := hweights z' pi' t hsub' x hxt
    have hcommon (k : Fin (N + 1)) (hk : 0 < w k) :
        ambientGridCorner h z pi k ∈ (s ∩ t : Set E) := by
      let a : Real := ∑ l, if k < l then w l else 0
      let r : Real := a + w k / 2
      have ha0 : 0 ≤ a := Finset.sum_nonneg fun l _ => by
        split_ifs
        · exact hw0 l
        · exact le_rfl
      have hb1 : a + w k ≤ 1 := by
        rw [← hw1]
        calc
          a + w k = ∑ l, ((if k < l then w l else 0) + if l = k then w k else 0) := by
            simp [a, Finset.sum_add_distrib]
          _ ≤ ∑ l, w l := Finset.sum_le_sum fun l _ => by
            split_ifs <;> simp_all
      have hr0 : 0 < r := by dsimp [r]; linarith
      have hr1 : r < 1 := by dsimp [r]; linarith
      have hra : a ≤ r := by dsimp [r]; linarith
      have hrb : r < ∑ l, if k ≤ l then w l else 0 := by
        have he : (∑ l, if k ≤ l then w l else 0) = a + w k := by
          calc
            _ = ∑ l, ((if k < l then w l else 0) + if l = k then w k else 0) := by
              apply Finset.sum_congr rfl
              intro l _
              split_ifs <;> simp_all <;> omega
            _ = _ := by simp [a, Finset.sum_add_distrib]
        rw [he]
        dsimp [r]
        linarith
      obtain ⟨j, hj, hja, hjb⟩ := hthreshold w' hw0' hw1' r hr0 hr1
      have he := (hround z pi w hw0 hw1 x hwx k r hr0 hr1 hra hrb).trans
        (hround z' pi' w' hw0' hw1' x hwx' j r hr0 hr1 hja hjb).symm
      exact ⟨hws k hk, he.symm ▸ hwt j hj⟩
    let I := Finset.univ.filter (fun k : Fin (N + 1) => 0 < w k)
    have hwzero (k : Fin (N + 1)) (hk : k ∉ I) : w k = 0 := by
      have hn : ¬0 < w k := by simpa [I] using hk
      exact le_antisymm (le_of_not_gt hn) (hw0 k)
    have hsum : ∑ k ∈ I, w k = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.subset_univ I) fun k _ hk => hwzero k hk
    have hsumx : ∑ k ∈ I, w k • ambientGridCorner h z pi k = x := by
      rw [← hwx]
      exact Finset.sum_subset (Finset.subset_univ I) fun k _ hk => by rw [hwzero k hk, zero_smul]
    apply mem_convexHull_of_exists_fintype (fun k : I => w k)
      (fun k : I => ambientGridCorner h z pi k) (fun k => hw0 k)
    · simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
    · intro k
      exact hcommon k (Finset.mem_filter.mp k.property).2
    · rw [Finset.univ_eq_attach]
      exact (Finset.sum_attach I
        (fun k : Fin (N + 1) => w k • ambientGridCorner h z pi k)).trans hsumx
  let K : Geometry.SimplicialComplex Real E :=
    { faces := ambientGridFaces h B
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts htn
        obtain ⟨_, z, pi, hz, hsub⟩ := hs
        exact ⟨htn, z, pi, hz, hts.trans hsub⟩
      indep := by
        intro s hs
        obtain ⟨hs, z, pi, _, hsub⟩ := hs
        exact (ambient_grid_simplex_geometry h hh z pi s hs hsub).1
      inter_subset_convexHull := fun hs ht => hinter _ _ hs ht }
  refine ⟨K, rfl, ?_, ?_⟩
  · let Z := Fintype.piFinset (fun _ : Fin N => Finset.Ico (-(B : Int)) B)
    let Q : Finset (Finset E) := Z.biUnion fun z =>
      Finset.univ.biUnion fun pi : Equiv.Perm (Fin N) => (ambientGridSimplex h z pi).powerset
    apply Q.finite_toSet.subset
    rintro s ⟨_, z, pi, hz, hsub⟩
    exact Finset.mem_biUnion.mpr ⟨z, Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_Ico.mpr (hz i), Finset.mem_biUnion.mpr
        ⟨pi, Finset.mem_univ _, Finset.mem_powerset.mpr hsub⟩⟩
  · ext x
    rw [Geometry.SimplicialComplex.mem_space_iff]
    constructor
    · rintro ⟨s, ⟨_, z, pi, hz, hsub⟩, hx⟩ i
      have hb := hbox z pi x (convexHull_mono hsub hx) i
      have hl : -(B : Real) ≤ (z i : Real) := by exact_mod_cast (hz i).1
      have hu : (z i : Real) + 1 ≤ (B : Real) := by
        exact_mod_cast (show z i + 1 ≤ (B : Int) from Int.add_one_le_iff.mpr (hz i).2)
      constructor <;> nlinarith
    · intro hx
      have hdiv (i : Fin N) : -(B : Real) ≤ x i / h ∧ x i / h ≤ (B : Real) := by
        constructor
        · exact (le_div_iff₀ hh).2 (by nlinarith [(hx i).1])
        · exact (div_le_iff₀ hh).2 (by nlinarith [(hx i).2])
      let z (i : Fin N) : Int := if x i / h = (B : Real) then (B : Int) - 1 else ⌊x i / h⌋
      let t (i : Fin N) : Real := x i / h - (z i : Real)
      have hz (i : Fin N) : -(B : Int) ≤ z i ∧ z i < B := by
        dsimp only [z]
        split_ifs with hi
        · constructor <;> omega
        · exact ⟨Int.le_floor.mpr (by simpa using (hdiv i).1),
            Int.floor_lt.mpr (lt_of_le_of_ne (hdiv i).2 hi)⟩
      have ht (i : Fin N) : 0 ≤ t i ∧ t i ≤ 1 := by
        dsimp only [t, z]
        split_ifs with hi
        · rw [hi]
          push_cast
          constructor <;> linarith
        · constructor
          · exact sub_nonneg.mpr (Int.floor_le _)
          · linarith [Int.lt_floor_add_one (x i / h)]
      let r (i j : Fin N) := t j < t i ∨ (t i = t j ∧ i ≤ j)
      let : IsTrans (Fin N) r := ⟨by
        intro i j k hij hjk
        dsimp only [r] at *
        rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hjk with hjk | ⟨hjk, hjk'⟩
        · exact Or.inl (hjk.trans hij)
        · exact Or.inl (hjk ▸ hij)
        · exact Or.inl (hij.symm ▸ hjk)
        · exact Or.inr ⟨hij.trans hjk, hij'.trans hjk'⟩⟩
      let : Std.Antisymm r := ⟨by
        intro i j hij hji
        dsimp only [r] at *
        rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hji with hji | ⟨hji, hji'⟩
        · linarith
        · linarith
        · linarith
        · exact le_antisymm hij' hji'⟩
      let : Std.Total r := ⟨by
        intro i j
        rcases lt_trichotomy (t i) (t j) with hij | hij | hij
        · exact Or.inr (Or.inl hij)
        · rcases le_total i j with hij' | hji'
          · exact Or.inl (Or.inr ⟨hij, hij'⟩)
          · exact Or.inr (Or.inr ⟨hij.symm, hji'⟩)
        · exact Or.inl (Or.inl hij)⟩
      let l := Finset.univ.sort r
      have hlen : l.length = N := by simp [l]
      let f (k : Fin N) : Fin N := l.get (Fin.cast hlen.symm k)
      have hf : Function.Bijective f := by
        constructor
        · intro i j hij
          have he := (Finset.sort_nodup Finset.univ r).get_inj_iff.mp hij
          exact Fin.ext (congrArg (fun q : Fin l.length => q.val) he)
        · intro i
          have hi : i ∈ l := (Finset.mem_sort r).2 (Finset.mem_univ i)
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
          exact ⟨Fin.cast hlen j, by simpa [f] using hj⟩
      let pi := Equiv.ofBijective f hf
      have hpi (i j : Fin N) (hij : i ≤ j) : t (pi j) ≤ t (pi i) := by
        rcases eq_or_lt_of_le hij with rfl | hij
        · exact le_rfl
        have hr := (Finset.pairwise_sort Finset.univ r).rel_get_of_lt
          (a := Fin.cast hlen.symm i) (b := Fin.cast hlen.symm j) hij
        exact hr.elim le_of_lt (fun h => h.1.ge)
      have htel (m : Nat) (a : Fin (m + 1) → Real) :
          (∑ k : Fin m, (a k.castSucc - a k.succ)) = a 0 - a (Fin.last m) := by
        rw [Finset.sum_sub_distrib]
        have h1 := Fin.sum_univ_succ a
        have h2 := Fin.sum_univ_castSucc a
        linarith
      have htail (m : Nat) (a : Fin (m + 1) → Real) (j : Fin m) :
          (∑ k : Fin m, if j < k then a k.castSucc - a k.succ else 0) =
            a j.succ - a (Fin.last m) := by
        let a' (k : Fin (m + 1)) := if k.val ≤ j.val then a j.succ else a k
        have he (k : Fin m) : a' k.castSucc - a' k.succ =
            if j < k then a k.castSucc - a k.succ else 0 := by
          dsimp only [a']
          simp only [Fin.val_castSucc, Fin.val_succ]
          by_cases hkj : k < j
          · have hle : k.val ≤ j.val := (show k.val < j.val from hkj).le
            have hle' : k.val + 1 ≤ j.val := by change k.val < j.val at hkj; omega
            simp only [if_pos hle, if_pos hle', if_neg (not_lt_of_ge hkj.le), sub_self]
          · by_cases heq : k = j
            · subst k
              simp
            · have hlt : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (Ne.symm heq)
              have hnot : ¬k.val ≤ j.val := not_le_of_gt hlt
              have hnot' : ¬k.val + 1 ≤ j.val := by change j.val < k.val at hlt; omega
              simp only [if_neg hnot, if_neg hnot', if_pos hlt]
        have hg := htel m a'
        simp only [he] at hg
        simpa [a', show ¬m ≤ j.val by omega] using hg
      let a (k : Fin (N + 2)) : Real :=
        if hk : k.val = 0 then 1 else
          if hk' : k.val ≤ N then t (pi ⟨k.val - 1, by omega⟩) else 0
      let w (k : Fin (N + 1)) : Real := a k.castSucc - a k.succ
      have ha0 : a 0 = 1 := by simp [a]
      have haN : a (Fin.last (N + 1)) = 0 := by simp [a]
      have hw0 (k : Fin (N + 1)) : 0 ≤ w k := by
        by_cases hk0 : k.val = 0
        · have he : k = 0 := Fin.ext hk0
          subst k
          by_cases hn : 0 < N
          · simpa [w, a, hn, show 1 ≤ N by omega] using sub_nonneg.mpr (ht (pi ⟨0, hn⟩)).2
          · have hN : N = 0 := by omega
            subst N
            simp [w, a]
        · by_cases hkN : k.val < N
          · have hp := hpi ⟨k.val - 1, by omega⟩ ⟨k.val, hkN⟩ (by change k.val - 1 ≤ k.val; omega)
            simpa [w, a, hk0, show k ≠ 0 from fun he => hk0 (congrArg Fin.val he),
              hkN, show k.val ≤ N by omega,
              show k.val + 1 ≠ 0 by omega, show k.val + 1 ≤ N by omega] using sub_nonneg.mpr hp
          · have he : k.val = N := by omega
            simpa [w, a, hk0, show k ≠ 0 from fun he => hk0 (congrArg Fin.val he),
              he, show N ≠ 0 by omega,
              show ¬N + 1 ≤ N by omega] using (ht (pi ⟨N - 1, by omega⟩)).1
      have hw1 : ∑ k, w k = 1 := by
        simpa only [w, ha0, haN, sub_zero] using htel (N + 1) a
      have hwt (i : Fin N) :
          (∑ k : Fin (N + 1), if (pi.symm i).val < k.val then w k else 0) = t i := by
        have he := htail (N + 1) a (pi.symm i).castSucc
        simpa [w, a, Fin.lt_def, show (pi.symm i).val + 1 ≠ 0 by omega,
          show (pi.symm i).val + 1 ≤ N by omega] using he
      have hwx : ∑ k, w k • ambientGridCorner h z pi k = x := by
        ext i
        rw [hmean z pi w hw1 i, hwt]
        dsimp only [t]
        field_simp
        ring
      refine ⟨ambientGridSimplex h z pi, ⟨?_, z, pi, hz, Finset.Subset.refl _⟩, ?_⟩
      · exact ⟨ambientGridCorner h z pi 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
      · exact mem_convexHull_of_exists_fintype w (ambientGridCorner h z pi) hw0 hw1
          (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) hwx

end PoincareConjecture.Proofs.M02.Topology
