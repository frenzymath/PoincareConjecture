import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcTerminalGaps
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Crosscut
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.NoninterlacingMatching
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Nat.Even










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

private theorem terminal_bit_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  exact hb.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

private theorem exists_terminal_active_embedding {k : ℕ} (hk : 2 ≤ k)
    (U V : Prop) [Decidable U] [Decidable V] :
    let m := k - 1 + (if U then 1 else 0) + (if V then 1 else 0)
    let o := if U then 0 else 1
    ∃ e : Fin m ↪ Fin (k + 1), (∀ i, (e i).val = o + i.val) ∧
      (∀ i : Fin (k + 1), (∃ a, e a = i) ↔
        (i = 0 ∧ U) ∨ (i = Fin.last k ∧ V) ∨ (i ≠ 0 ∧ i ≠ Fin.last k)) ∧ 0 < m := by
  dsimp only
  let m := k - 1 + (if U then 1 else 0) + (if V then 1 else 0)
  let o := if U then 0 else 1
  have hbound : o + m ≤ k + 1 := by
    by_cases hU : U <;> by_cases hV : V <;> simp [m, o, hU, hV] <;> omega
  let e : Fin m ↪ Fin (k + 1) :=
    ⟨fun i => ⟨o + i.val, by have := i.isLt; omega⟩, by
      intro i j h
      apply Fin.ext
      have hh := congrArg Fin.val h
      change o + i.val = o + j.val at hh
      omega⟩
  have hrange (i : Fin (k + 1)) :
      (∃ a, e a = i) ↔ o ≤ i.val ∧ i.val < o + m := by
    constructor
    · rintro ⟨a, rfl⟩
      change o ≤ o + a.val ∧ o + a.val < o + m
      have := a.isLt
      omega
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨i.val - o, by omega⟩, ?_⟩
      apply Fin.ext
      change o + (i.val - o) = i.val
      omega
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro i
    rw [hrange]
    have hi := i.isLt
    by_cases hU : U <;> by_cases hV : V <;>
      simp only [m, o, hU, hV, if_true, if_false, ne_eq, Fin.ext_iff, Fin.val_zero,
        Fin.val_last, and_true, and_false, false_or] <;> omega
  · omega

private theorem exists_actual_terminal_pairing {k m : ℕ}
    (τ : Fin (k + 1) ≃ Fin (k + 1)) (B : Finset (Fin k))
    (e : Fin m ↪ Fin (k + 1))
    (hcover : ∀ i : Fin (k + 1), (∃ a, e a = i) ↔
      ∃ j : Fin k, j ∈ B ∧ (τ j.castSucc = i ∨ τ j.succ = i))
    (hunique : ∀ i : Fin (k + 1), ∀ a ∈ B, ∀ b ∈ B,
      (τ a.castSucc = i ∨ τ a.succ = i) →
      (τ b.castSucc = i ∨ τ b.succ = i) → a = b) :
    ∃ ι : {j : Fin k // j ∈ B} × Fin 2 ≃ Fin m,
      (∀ a, e (ι (a, 0)) = τ a.val.castSucc) ∧
      (∀ a, e (ι (a, 1)) = τ a.val.succ) ∧
      ∃ M : Fin m → Fin m, Function.Involutive M ∧ (∀ i, M i ≠ i) ∧
        (∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b)) ∧
        (∀ i j, j ≠ i → j ≠ M i → (ι.symm i).1 ≠ (ι.symm j).1) ∧ Even m := by
  classical
  let endpoint := fun x : {j : Fin k // j ∈ B} × Fin 2 =>
    if x.2 = 0 then τ x.1.val.castSucc else τ x.1.val.succ
  have hinc (x : {j : Fin k // j ∈ B} × Fin 2) :
      τ x.1.val.castSucc = endpoint x ∨ τ x.1.val.succ = endpoint x := by
    by_cases h : x.2 = 0
    · exact Or.inl (by simp only [endpoint, if_pos h])
    · exact Or.inr (by simp only [endpoint, if_neg h])
  have hexists (x : {j : Fin k // j ∈ B} × Fin 2) : ∃ i, e i = endpoint x :=
    (hcover _).mpr ⟨x.1.val, x.1.property, hinc x⟩
  let f := fun x : {j : Fin k // j ∈ B} × Fin 2 => Classical.choose (hexists x)
  have hf (x : {j : Fin k // j ∈ B} × Fin 2) : e (f x) = endpoint x :=
    Classical.choose_spec (hexists x)
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ heq
      have hep : endpoint (a, b) = endpoint (a', b') :=
        (hf _).symm.trans ((congrArg e heq).trans (hf _))
      have ha : a = a' := Subtype.ext (hunique _ a.val a.property a'.val a'.property
        (hinc (a, b)) (hep.symm ▸ hinc (a', b')))
      subst a'
      congr 1
      rcases terminal_bit_cases b with rfl | rfl <;>
        rcases terminal_bit_cases b' with rfl | rfl
      · rfl
      · have hv := congrArg Fin.val (τ.injective (by
          simpa only [endpoint, if_pos rfl, show (1 : Fin 2) ≠ 0 by decide, if_false]
            using hep))
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      · have hv := congrArg Fin.val (τ.injective (by
          simpa only [endpoint, if_pos rfl, show (1 : Fin 2) ≠ 0 by decide, if_false]
            using hep))
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      · rfl
    · intro i
      obtain ⟨j, hj, he⟩ := (hcover (e i)).mp ⟨i, rfl⟩
      rcases he with he | he
      · refine ⟨(⟨j, hj⟩, 0), e.injective ((hf _).trans ?_)⟩
        simpa only [endpoint, if_pos rfl] using he
      · refine ⟨(⟨j, hj⟩, 1), e.injective ((hf _).trans ?_)⟩
        simpa only [endpoint, show (1 : Fin 2) ≠ 0 by decide, if_false] using he
  let ι := Equiv.ofBijective f hbij
  let S : {j : Fin k // j ∈ B} × Fin 2 ≃ {j : Fin k // j ∈ B} × Fin 2 :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)
  let M : Fin m → Fin m := fun i => ι (S (ι.symm i))
  have hS (x : {j : Fin k // j ∈ B} × Fin 2) : S (S x) = x := by
    obtain ⟨a, b⟩ := x
    change (a, Equiv.swap 0 1 (Equiv.swap 0 1 b)) = (a, b)
    rw [Equiv.swap_apply_self]
  have hM : Function.Involutive M := by
    intro i
    dsimp only [M]
    rw [ι.symm_apply_apply, hS, ι.apply_symm_apply]
  have hmate (a : {j : Fin k // j ∈ B}) (b : Fin 2) :
      M (ι (a, b)) = ι (a, Equiv.swap 0 1 b) := by
    dsimp only [M]
    rw [ι.symm_apply_apply]
    rfl
  have hne (i : Fin m) : M i ≠ i := by
    intro heq
    have heq' : S (ι.symm i) = ι.symm i :=
      ι.injective (heq.trans (ι.apply_symm_apply i).symm)
    have hb := congrArg Prod.snd heq'
    change Equiv.swap 0 1 (ι.symm i).2 = (ι.symm i).2 at hb
    rcases terminal_bit_cases (ι.symm i).2 with h0 | h1
    · rw [h0, Equiv.swap_apply_left] at hb
      have := congrArg Fin.val hb
      omega
    · rw [h1, Equiv.swap_apply_right] at hb
      have := congrArg Fin.val hb
      omega
  refine ⟨ι, ?_, ?_, M, hM, hne, hmate, ?_, ?_⟩
  · intro a
    simpa only [ι, Equiv.ofBijective_apply, endpoint, if_pos rfl] using hf (a, 0)
  · intro a
    simpa only [ι, Equiv.ofBijective_apply, endpoint, show (1 : Fin 2) ≠ 0 by decide,
      if_false] using hf (a, 1)
  · intro i j hji hjM heq
    obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
    obtain ⟨⟨a', b'⟩, rfl⟩ := ι.surjective j
    simp only [ι.symm_apply_apply] at heq
    change a = a' at heq
    subst a'
    rcases terminal_bit_cases b with rfl | rfl <;>
      rcases terminal_bit_cases b' with rfl | rfl
    · exact hji rfl
    · exact hjM (by simpa only [Equiv.swap_apply_left] using (hmate a 0).symm)
    · exact hjM (by simpa only [Equiv.swap_apply_right] using (hmate a 1).symm)
    · exact hji rfl
  · have hc := Fintype.card_congr ι
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    exact ⟨Fintype.card {j : Fin k // j ∈ B}, by omega⟩

private theorem terminal_pair_orientation {k m : ℕ} (B : Finset (Fin k))
    (ι : {j : Fin k // j ∈ B} × Fin 2 ≃ Fin m) (M : Fin m → Fin m)
    (hmate : ∀ a b, M (ι (a, b)) = ι (a, Equiv.swap 0 1 b)) (i : Fin m) :
    (i = ι ((ι.symm i).1, 0) ∧ M i = ι ((ι.symm i).1, 1)) ∨
      (i = ι ((ι.symm i).1, 1) ∧ M i = ι ((ι.symm i).1, 0)) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
  simp only [ι.symm_apply_apply]
  rcases terminal_bit_cases b with rfl | rfl
  · exact Or.inl ⟨rfl, by simpa only [Equiv.swap_apply_left] using hmate a 0⟩
  · exact Or.inr ⟨rfl, by simpa only [Equiv.swap_apply_right] using hmate a 1⟩

private theorem terminal_gaps_separated {k : ℕ}
    (τ : Fin (k + 1) ≃ Fin (k + 1)) (B : Finset (Fin k))
    (hunique : ∀ i : Fin (k + 1), ∀ a ∈ B, ∀ b ∈ B,
      (τ a.castSucc = i ∨ τ a.succ = i) →
      (τ b.castSucc = i ∨ τ b.succ = i) → a = b)
    (a b : {j : Fin k // j ∈ B}) (hne : a ≠ b) :
    a.val.val + 1 < b.val.val ∨ b.val.val + 1 < a.val.val := by
  have htouch (x y : {j : Fin k // j ∈ B}) (hxy : x ≠ y)
      (h : x.val.val + 1 = y.val.val) : False := by
    apply hxy
    apply Subtype.ext
    exact hunique (τ x.val.succ) x.val x.property y.val y.property (Or.inr rfl)
      (Or.inl (congrArg τ (Fin.ext h.symm)))
  have hab : a.val.val ≠ b.val.val := fun h => hne (Subtype.ext (Fin.ext h))
  have hleft : a.val.val + 1 ≠ b.val.val := htouch a b hne
  have hright : b.val.val + 1 ≠ a.val.val := htouch b a hne.symm
  omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open scoped Classical in



theorem IsSimplePolygonalArc.exists_terminal_path_inside_matching {n k : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (hk : 2 ≤ k)
    (c : Fin (k + 1) ↪ Fin (n + 2))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hadj : c (Fin.last k) = (finRotate (n + 2)).symm (c 0) ∨
      c (Fin.last k) = finRotate (n + 2) (c 0))
    (hwnot : (if c (Fin.last k) = (finRotate (n + 2)).symm (c 0)
      then finRotate (n + 2) (c 0) else (finRotate (n + 2)).symm (c 0)) ∉ range c) :
    let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
    let u := c 0
    let v := c (Fin.last k)
    let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
      else (finRotate (n + 2)).symm u
    let z := if v = (finRotate (n + 2)).symm u then (finRotate (n + 2)).symm v
      else finRotate (n + 2) v
    let I := polygonInterior r
    let O := polygonExterior r
    let U := AffineMap.lineMap (p u) (p w) (1 / 2 : ℝ) ∈ I
    let V := AffineMap.lineMap (p v) (p z) (1 / 2 : ℝ) ∈ I
    IsSimplePolygon r →
    r.boundary ℝ ∩ polygonArcBoundary p = range r ∪ segment ℝ (p v) (p u) →
    p 0 ∈ O → p (Fin.last (n + 1)) ∈ O →
    (∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
        IsOpen W ∧ r i ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
        A ∪ B = W \ r.boundary ℝ ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p ((finRotate (n + 2)).symm (c i))) t ∈ A) ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p (finRotate (n + 2) (c i))) t ∈ B)) →
    let m := k - 1 + (if U then 1 else 0) + (if V then 1 else 0)
    let o := if U then 0 else 1
    ∃ e : Fin m ↪ Fin (k + 1), (∀ i, (e i).val = o + i.val) ∧
      ∃ M : Fin m → Fin m,
        let T := fun i => polygonLinearParameter p '' Icc
          (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
          (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
        let S := fun i => polygonLinearParameter p '' Ioo
          (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
          (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
        let γ := fun i (t : ℝ) => polygonLinearParameter p
          (AffineMap.lineMap ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) t)
        IsNoninterlacingMatching M ∧ Even m ∧ 2 ≤ m ∧
        (∀ t ∈ Ioo (0 : ℝ) 1,
          (AffineMap.lineMap (p u) (p w) t ∈ I ↔ U) ∧
          (AffineMap.lineMap (p u) (p w) t ∈ O ↔ ¬ U) ∧
          (AffineMap.lineMap (p v) (p z) t ∈ I ↔ V) ∧
          (AffineMap.lineMap (p v) (p z) t ∈ O ↔ ¬ V)) ∧
        (¬ U → p w ∈ O) ∧
        (∀ i, e i = 0 → p w ∈ S i) ∧ (∀ i, S i ⊆ I) ∧
        (∀ i, T i ∩ r.boundary ℝ = {r (e i), r (e (M i))}) ∧
        (∀ i, ∃ ell : ℕ, ∃ q : Polygon E (ell + 2),
          ell + 1 = Nat.dist (c (e i)).val (c (e (M i))).val ∧
          IsSimplePolygonalArc q ∧ q 0 = p (c (e i)) ∧
          q (Fin.last (ell + 1)) = p (c (e (M i))) ∧
          (∀ j : Fin (ell + 2), q j = polygonLinearParameter p
            (if c (e i) < c (e (M i)) then ((c (e i)).val : ℝ) + j.val
              else ((c (e i)).val : ℝ) - j.val)) ∧
          (∀ t ∈ Icc (0 : ℝ) (ell + 1 : ℕ), polygonLinearParameter q t =
            polygonLinearParameter p (if c (e i) < c (e (M i))
              then ((c (e i)).val : ℝ) + t else ((c (e i)).val : ℝ) - t)) ∧
          polygonArcBoundary q = T i ∧
          polygonArcBoundary q \ {p (c (e i)), p (c (e (M i)))} = S i) ∧
        (∀ i j, j ≠ i → j ≠ M i → Disjoint (T i) (T j)) ∧
        (∀ i, T (M i) = T i) ∧ (∀ i, S (M i) = S i) ∧
        (∀ i t, γ (M i) t = γ i (1 - t)) := by
  classical
  dsimp only
  intro hr hcontact hfirst hlast hcross
  let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
  let u := c 0
  let v := c (Fin.last k)
  let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
    else (finRotate (n + 2)).symm u
  let z := if v = (finRotate (n + 2)).symm u then (finRotate (n + 2)).symm v
    else finRotate (n + 2) v
  let U := AffineMap.lineMap (p u) (p w) (1 / 2 : ℝ) ∈ polygonInterior r
  let V := AffineMap.lineMap (p v) (p z) (1 / 2 : ℝ) ∈ polygonInterior r
  let m := k - 1 + (if U then 1 else 0) + (if V then 1 else 0)
  let o := if U then 0 else 1
  obtain ⟨τ, B, hτ, hB, hcover, hunique, _, hrays, hwO, hwI⟩ :=
    hp.exists_terminal_inside_gaps hdim hk c hint hadj hwnot
      hr hcontact hfirst hlast hcross
  obtain ⟨e, he, hecover, hmpos⟩ := exists_terminal_active_embedding hk U V
  obtain ⟨ι, hι0, hι1, M, hM, hne, hmate, hkeys, heven⟩ :=
    exists_actual_terminal_pairing τ B e (fun i => (hecover i).trans (hcover i)) hunique
  have htwo : 2 ≤ m := by obtain ⟨a, ha⟩ := heven; omega
  let key := fun i => (ι.symm i).1
  let T := fun i => polygonLinearParameter p '' Icc
    (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
    (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
  let S := fun i => polygonLinearParameter p '' Ioo
    (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
    (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
  let γ := fun i (t : ℝ) => polygonLinearParameter p
    (AffineMap.lineMap ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) t)
  have hbounds (i : Fin m) :
      min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) =
        ((c (τ (key i).val.castSucc)).val : ℝ) ∧
      max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) =
        ((c (τ (key i).val.succ)).val : ℝ) := by
    obtain ⟨⟨a, b⟩, rfl⟩ := ι.surjective i
    rw [hmate]
    simp only [key, ι.symm_apply_apply]
    have hle : ((c (τ a.val.castSucc)).val : ℝ) ≤ ((c (τ a.val.succ)).val : ℝ) := by
      exact_mod_cast (hτ (show a.val.castSucc < a.val.succ from by
        change a.val.val < a.val.val + 1; omega)).le
    rcases terminal_bit_cases b with rfl | rfl
    · simp only [Equiv.swap_apply_left, hι0, hι1, min_eq_left hle, max_eq_right hle,
        and_self]
    · simp only [Equiv.swap_apply_right, hι0, hι1, min_eq_right hle, max_eq_left hle,
        and_self]
  have hsets (i : Fin m) :
      T i = polygonLinearParameter p '' Icc
        ((c (τ (key i).val.castSucc)).val : ℝ) ((c (τ (key i).val.succ)).val : ℝ) ∧
      S i = polygonLinearParameter p '' Ioo
        ((c (τ (key i).val.castSucc)).val : ℝ) ((c (τ (key i).val.succ)).val : ℝ) := by
    simp only [T, S, (hbounds i).1, (hbounds i).2, and_self]
  have hopen (i : Fin m) : S i ⊆ polygonInterior r := by
    rw [(hsets i).2]
    exact (hB (key i).val).mp (key i).property
  have hci (i : Fin m) : c (e i) ≠ c (e (M i)) := fun h =>
    hne i (e.injective (c.injective h)).symm
  have hq (i : Fin m) :
      ∃ ell : ℕ, ∃ q : Polygon E (ell + 2),
        ell + 1 = Nat.dist (c (e i)).val (c (e (M i))).val ∧
        IsSimplePolygonalArc q ∧ q 0 = p (c (e i)) ∧
        q (Fin.last (ell + 1)) = p (c (e (M i))) ∧
        (∀ j : Fin (ell + 2), q j = polygonLinearParameter p
          (if c (e i) < c (e (M i)) then ((c (e i)).val : ℝ) + j.val
            else ((c (e i)).val : ℝ) - j.val)) ∧
        (∀ t ∈ Icc (0 : ℝ) (ell + 1 : ℕ), polygonLinearParameter q t =
          polygonLinearParameter p (if c (e i) < c (e (M i))
            then ((c (e i)).val : ℝ) + t else ((c (e i)).val : ℝ) - t)) ∧
        polygonArcBoundary q = T i ∧
        polygonArcBoundary q \ {p (c (e i)), p (c (e (M i)))} = S i :=
    hp.exists_consecutive_subarc (c (e i)) (c (e (M i))) (hci i)
  have hincidence (i : Fin m) : T i ∩ r.boundary ℝ = {r (e i), r (e (M i))} := by
    obtain ⟨ell, q, _, _, _, _, _, _, hT, hS⟩ := hq i
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hn
      have hxS : x ∈ S i := hS ▸ ⟨hT.symm ▸ hx.1, hn⟩
      exact (hopen i hxS).1 hx.2
    · rintro x (rfl | rfl)
      · exact ⟨⟨(c (e i)).val, ⟨min_le_left _ _, le_max_left _ _⟩,
          polygonLinearParameter_natVertex p _⟩, polygon_vertex_mem_boundary r _⟩
      · exact ⟨⟨(c (e (M i))).val, ⟨min_le_right _ _, le_max_right _ _⟩,
          polygonLinearParameter_natVertex p _⟩, polygon_vertex_mem_boundary r _⟩
  have hindex (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ n + 1 from by omega)⟩
  have hdom (i : Fin m) {t : ℝ}
      (ht : t ∈ Icc (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
        (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))) :
      t ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨(le_min (hindex (c (e i))).1 (hindex (c (e (M i)))).1).trans ht.1,
      ht.2.trans (max_le (hindex (c (e i))).2 (hindex (c (e (M i)))).2)⟩
  have horder (i j : Fin m) (hs : (key i).val.val + 1 < (key j).val.val) :
      max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) <
        min ((c (e j)).val : ℝ) ((c (e (M j))).val : ℝ) := by
    rw [(hbounds i).2, (hbounds j).1]
    exact_mod_cast hτ (show (key i).val.succ < (key j).val.castSucc from hs)
  have hdis (i j : Fin m) (hji : j ≠ i) (hjM : j ≠ M i) : Disjoint (T i) (T j) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have hab := hp.injOn_polygonLinearParameter (hdom i ha) (hdom j hb) hba.symm
    subst b
    rcases terminal_gaps_separated τ B hunique (key i) (key j)
      (hkeys i j hji hjM) with hs | hs
    · exact (not_lt_of_ge (hb.1.trans ha.2)) (horder i j hs)
    · exact (not_lt_of_ge (ha.1.trans hb.2)) (horder j i hs)
  have hcurve (i : Fin m) : γ i '' Ioo (0 : ℝ) 1 ⊆ S i := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨AffineMap.lineMap ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ) t, ?_, rfl⟩
    have hv : (c (e i)).val ≠ (c (e (M i))).val := fun h => hci i (Fin.ext h)
    have hreal : ((c (e i)).val : ℝ) ≠ ((c (e (M i))).val : ℝ) := by exact_mod_cast hv
    rcases lt_or_gt_of_ne hreal with hab | hba
    · simp only [min_eq_left hab.le, max_eq_right hab.le, mem_Ioo,
        AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hab) ht.1,
        mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    · simp only [min_eq_right hba.le, max_eq_left hba.le, mem_Ioo,
        AffineMap.lineMap_apply_ring]
      constructor <;> nlinarith [mul_pos (sub_pos.mpr hba) ht.1,
        mul_pos (sub_pos.mpr hba) (sub_pos.mpr ht.2)]
  have hΓ : Continuous (polygonLinearParameter p) :=
    (continuous_polygonLinearParameter (p := fun _ : Unit => p)
      (fun _ => continuous_const)).comp
      ((continuous_const : Continuous (fun _ : ℝ => ())).prodMk continuous_id)
  have hemono : StrictMono (fun i : Fin m => (e i).val) := by
    intro i j hij
    change (e i).val < (e j).val
    rw [he, he]
    exact Nat.add_lt_add_left hij o
  have hnon : IsNoninterlacingMatching M := by
    refine ⟨hM, hne, ?_⟩
    intro a b hab hbMa hMaMb
    obtain ⟨ell, q, _, hs, hq0, hq1, _, _, hT, hS⟩ := hq a
    have hdist (x : Fin m) (hx : a ≤ x) :
        cyclicDistance (e a) (e x) = (e x).val - (e a).val :=
      Fin.sub_val_of_le (hemono.monotone hx)
    have hf0 : γ b 0 = r (e b) := by
      simp only [γ, AffineMap.lineMap_apply_zero, polygonLinearParameter_natVertex]; rfl
    have hf1 : γ b 1 = r (e (M b)) := by
      simp only [γ, AffineMap.lineMap_apply_one, polygonLinearParameter_natVertex]; rfl
    obtain ⟨t, ht, hx⟩ := hr.crosscut_intersects_continuous_of_cyclic_order hs hdim
      (e a) (e (M a)) (e b) (e (M b)) hq0 hq1 (hS.symm ▸ hopen a) (γ b)
      (hΓ.comp AffineMap.lineMap_continuous).continuousOn hf0 hf1
      ((hcurve b).trans (hopen b))
      (by rw [hdist b hab.le, he, he]; omega)
      (by rw [hdist b hab.le, hdist (M a) (hab.trans hbMa).le, he, he, he]; omega)
      (by rw [hdist (M a) (hab.trans hbMa).le,
        hdist (M b) ((hab.trans hbMa).trans hMaMb).le, he, he, he]; omega)
    have hxA : γ b t ∈ T a := hT ▸ hx.1
    have hxB : γ b t ∈ T b := by
      obtain ⟨u, hu, heq⟩ := hcurve b ⟨t, ht, rfl⟩
      exact ⟨u, ⟨hu.1.le, hu.2.le⟩, heq⟩
    exact Set.disjoint_left.mp (hdis a b (ne_of_gt hab) (ne_of_lt hbMa)) hxA hxB
  refine ⟨e, he, M, hnon, heven, htwo, hrays, hwO, ?_, hopen, hincidence, hq, hdis, ?_, ?_, ?_⟩
  · intro i hi
    change p w ∈ S i
    rw [(hsets i).2]
    apply hwI (key i).val (key i).property
    rcases terminal_pair_orientation B ι M hmate i with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact Or.inl ((hι0 (key i)).symm.trans ((congrArg e h0).symm.trans hi))
    · exact Or.inr ((hι1 (key i)).symm.trans ((congrArg e h1).symm.trans hi))
  · intro i
    change T (M i) = T i
    dsimp only [T]
    rw [hM i, min_comm ((c (e (M i))).val : ℝ) ((c (e i)).val : ℝ),
      max_comm ((c (e (M i))).val : ℝ) ((c (e i)).val : ℝ)]
  · intro i
    change S (M i) = S i
    dsimp only [S]
    rw [hM i, min_comm ((c (e (M i))).val : ℝ) ((c (e i)).val : ℝ),
      max_comm ((c (e (M i))).val : ℝ) ((c (e i)).val : ℝ)]
  · intro i t
    change γ (M i) t = γ i (1 - t)
    simp only [γ, hM i, AffineMap.lineMap_apply_one_sub]

end PoincareConjecture.M25.Topology3D
