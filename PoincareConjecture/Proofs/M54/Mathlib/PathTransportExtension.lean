import PoincareConjecture.Proofs.M54.Mathlib.LocalPathTransport
import PoincareConjecture.Proofs.M54.Mathlib.DyadicSubdivision
import PoincareConjecture.Proofs.M54.Mathlib.GridProduct










set_option autoImplicit false

open Set unitInterval

namespace LocalPathTransport

variable {X ι G : Type*} [TopologicalSpace X] {U : ι → Set X} [Monoid G]



def Subordinate (U : ι → Set X) (p : C(unitInterval, X)) (n : ℕ) : Prop :=
  ∀ k < 2 ^ n, ∃ i, MapsTo p (Icc (dyadicPoint n k) (dyadicPoint n (k + 1))) (U i)



theorem Subordinate.succ {p : C(unitInterval, X)} {n : ℕ} (h : Subordinate U p n) :
    Subordinate U p (n + 1) := by
  intro k hk
  have hk' : k / 2 < 2 ^ n := by
    rw [pow_succ] at hk
    omega
  obtain ⟨i, hi⟩ := h (k / 2) hk'
  exact ⟨i, hi.mono_left (dyadic_cell_subset n k)⟩



theorem Subordinate.mono {p : C(unitInterval, X)} {n m : ℕ}
    (h : Subordinate U p n) (hnm : n ≤ m) : Subordinate U p m := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact ih.succ



noncomputable def dyadicValue (L : LocalPathTransport U G) (p : C(unitInterval, X)) (n : ℕ) : G :=
  ((List.range (2 ^ n)).map (fun k =>
    L.value (p.intervalSubpath (dyadicPoint n k) (dyadicPoint n (k + 1))))).prod



theorem dyadicValue_succ (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {n : ℕ} (h : Subordinate U p n) : L.dyadicValue p (n + 1) = L.dyadicValue p n := by
  unfold dyadicValue
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n by omega, List.prod_range_pairs]
  congr 1
  apply List.map_congr_left
  intro k hk
  obtain ⟨i, hi⟩ := h k (List.mem_range.mp hk)
  have hleft : dyadicPoint n k ≤ dyadicPoint (n + 1) (2 * k + 1) := by
    rw [← dyadicPoint_even n k]
    exact dyadicPoint_mono _ (by omega)
  have hright : dyadicPoint (n + 1) (2 * k + 1) ≤ dyadicPoint n (k + 1) := by
    rw [← dyadicPoint_even n (k + 1)]
    exact dyadicPoint_mono _ (by omega)
  simpa only [dyadicPoint_even, show 2 * k + 1 + 1 = 2 * (k + 1) by omega] using
    L.interval_mul p hleft hright i hi



theorem dyadicValue_stable (L : LocalPathTransport U G) (p : C(unitInterval, X))
    {n m : ℕ} (h : Subordinate U p n) (hnm : n ≤ m) :
    L.dyadicValue p m = L.dyadicValue p n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (L.dyadicValue_succ p (h.mono hnm)).trans ih



theorem exists_subordinate (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) : ∃ n, Subordinate U p n := by
  apply exists_dyadic_subordinate (fun i => p ⁻¹' U i)
    (fun i => (hU i).preimage p.continuous)
  intro t _
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (p t)))
  exact mem_iUnion.mpr ⟨i, hi⟩



noncomputable def extend (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) : G :=
  L.dyadicValue p (Classical.choose (exists_subordinate hU hcover p))



theorem extend_eq_dyadicValue (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) {n : ℕ} (h : Subordinate U p n) :
    L.extend hU hcover p = L.dyadicValue p n := by
  let m := Classical.choose (exists_subordinate hU hcover p)
  have hm : Subordinate U p m := Classical.choose_spec (exists_subordinate hU hcover p)
  exact (L.dyadicValue_stable p hm (le_max_left m n)).symm.trans
    (L.dyadicValue_stable p h (le_max_right m n))



theorem extend_eq_local (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (p : C(unitInterval, X)) (i : ι) (hp : ∀ t, p t ∈ U i) :
    L.extend hU hcover p = L.value p := by
  have h : Subordinate U p 0 := fun _ _ => ⟨i, fun t _ => hp t⟩
  rw [L.extend_eq_dyadicValue hU hcover p h]
  have hlast : dyadicPoint 0 1 = 1 := dyadicPoint_last 0
  simp [dyadicValue, hlast]



theorem extend_const (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) (x : X) :
    L.extend hU hcover (.const _ x) = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ x))
  rw [L.extend_eq_local hU hcover (.const _ x) i (fun _ => hi), L.map_const]

private theorem horizontal_subordinate
    (H : C(unitInterval × unitInterval, X)) (n : ℕ)
    (hgrid : ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      MapsTo H (Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1))) (U i))
    (j : ℕ) (hj : j ≤ 2 ^ n) :
    Subordinate U (H.horizontalPath (dyadicPoint n j)) n := by
  have hpos : 0 < 2 ^ n := by positivity
  let l := min j (2 ^ n - 1)
  have hl : l < 2 ^ n := by dsimp [l]; omega
  have hlj : l ≤ j := min_le_left _ _
  have hjl : j ≤ l + 1 := by dsimp [l]; omega
  intro k hk
  obtain ⟨i, hi⟩ := hgrid k hk l hl
  exact ⟨i, fun t ht => hi ⟨ht, dyadicPoint_mono n hlj, dyadicPoint_mono n hjl⟩⟩

private theorem vertical_subordinate
    (H : C(unitInterval × unitInterval, X)) (n : ℕ)
    (hgrid : ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      MapsTo H (Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1))) (U i))
    (j : ℕ) (hj : j ≤ 2 ^ n) :
    Subordinate U (H.verticalPath (dyadicPoint n j)) n := by
  have hpos : 0 < 2 ^ n := by positivity
  let k := min j (2 ^ n - 1)
  have hk : k < 2 ^ n := by dsimp [k]; omega
  have hkj : k ≤ j := min_le_left _ _
  have hjk : j ≤ k + 1 := by dsimp [k]; omega
  intro l hl
  obtain ⟨i, hi⟩ := hgrid k hk l hl
  exact ⟨i, fun t ht => hi ⟨⟨dyadicPoint_mono n hkj, dyadicPoint_mono n hjk⟩, ht⟩⟩



theorem extend_square (L : LocalPathTransport U G)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (H : C(unitInterval × unitInterval, X)) :
    L.extend hU hcover (H.horizontalPath 0) * L.extend hU hcover (H.verticalPath 1) =
      L.extend hU hcover (H.verticalPath 0) * L.extend hU hcover (H.horizontalPath 1) := by
  obtain ⟨n, hn⟩ := exists_dyadic_square_subordinate (fun i => H ⁻¹' U i)
    (fun i => (hU i).preimage H.continuous) (by
      intro t _
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ (H t)))
      exact mem_iUnion.mpr ⟨i, hi⟩)
  let h := fun k l => L.value ((H.horizontalPath (dyadicPoint n l)).intervalSubpath
    (dyadicPoint n k) (dyadicPoint n (k + 1)))
  let v := fun k l => L.value ((H.verticalPath (dyadicPoint n k)).intervalSubpath
    (dyadicPoint n l) (dyadicPoint n (l + 1)))
  have hc : ∀ k < 2 ^ n, ∀ l < 2 ^ n,
      h k l * v (k + 1) l = v k l * h k (l + 1) := by
    intro k hk l hl
    obtain ⟨i, hi⟩ := hn k hk l hl
    have hs := L.square (H.rectangleRestrict (dyadicPoint n k) (dyadicPoint n (k + 1))
      (dyadicPoint n l) (dyadicPoint n (l + 1))) i (fun z => hi
        ⟨⟨Icc.le_convexComb (dyadicPoint_mono n (Nat.le_succ k)) z.1,
          Icc.convexComb_le (dyadicPoint_mono n (Nat.le_succ k)) z.1⟩,
         ⟨Icc.le_convexComb (dyadicPoint_mono n (Nat.le_succ l)) z.2,
          Icc.convexComb_le (dyadicPoint_mono n (Nat.le_succ l)) z.2⟩⟩)
    simpa [h, v] using hs
  have hb : Subordinate U (H.horizontalPath 0) n := by
    simpa using horizontal_subordinate (U := U) H n hn 0 (Nat.zero_le _)
  have ht : Subordinate U (H.horizontalPath 1) n := by
    simpa using horizontal_subordinate (U := U) H n hn (2 ^ n) le_rfl
  have hl : Subordinate U (H.verticalPath 0) n := by
    simpa using vertical_subordinate (U := U) H n hn 0 (Nat.zero_le _)
  have hr : Subordinate U (H.verticalPath 1) n := by
    simpa using vertical_subordinate (U := U) H n hn (2 ^ n) le_rfl
  rw [L.extend_eq_dyadicValue hU hcover _ hb, L.extend_eq_dyadicValue hU hcover _ hr,
    L.extend_eq_dyadicValue hU hcover _ hl, L.extend_eq_dyadicValue hU hcover _ ht]
  simpa [dyadicValue, h, v] using List.prod_range_grid h v (2 ^ n) (2 ^ n) hc

end LocalPathTransport
