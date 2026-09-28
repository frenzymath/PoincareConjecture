import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Counting.NormalCornerOrder
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Rectangles.AllCorners









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem origin_pair_parameters_eq {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ({(0, b), (a, 0)} : Set (ℝ × ℝ)) = {(0, v), (u, 0)}) : a = u ∧ b = v := by
  constructor
  · have hm := h.subset (show (a, (0 : ℝ)) ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ)) by simp)
    rcases hm with he | he
    · exact False.elim (ha.ne' (congrArg Prod.fst he))
    · exact congrArg Prod.fst (mem_singleton_iff.mp he)
  · have hm := h.subset (show ((0 : ℝ), b) ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ)) by simp)
    rcases hm with he | he
    · exact congrArg Prod.snd he
    · exact False.elim (hb.ne' (congrArg Prod.snd (mem_singleton_iff.mp he)))

theorem exists_distinct_successor_rectangle_family
    {ι : Type*} [Finite ι] (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hsub : ∀ k, D k ⊆ base)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hpv : ∀ k, p k ∉ vertices) (hqv : ∀ k, q k ∉ vertices)
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1}) :
    ∃ (c : ι → Fin 3) (a b : ι → ℝ),
      (∀ i, a i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, b i ∈ Ioo (0 : ℝ) 1) ∧
      (∀ i, cornerMap (c i) '' ({p i, q i} : Set (ℝ × ℝ)) = {(0, b i), (a i, 0)}) ∧
      Nat.card {i : ι // ∃ j, c j = c i ∧ a i < a j} + Nat.card (range c) = Nat.card ι ∧
      Nat.card (range c) ≤ 3 ∧
      ∃ (n : {i : ι // ∃ j, c j = c i ∧ a i < a j} → ι)
        (M : {i : ι // ∃ j, c j = c i ∧ a i < a j} → Set (ℝ × ℝ)),
        Function.Injective M ∧
        ∀ i, c (n i) = c i ∧ a i < a (n i) ∧
          IsFinitePLBallPair (ℝ × ℝ) (M i)
            (D i ∪ (D (n i) ∪ cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i)))) ∧
          M i ∩ frontier base = cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i)) ∧
          (∀ k : ι, k ≠ (i : ι) → k ≠ n i → Disjoint (D k) (M i)) ∧
          (∀ x ∈ M i \ (D i ∪ D (n i)),
            connectedComponentIn (base \ ⋃ k, D k) x = M i \ (D i ∪ D (n i)) ∧
            closure (connectedComponentIn (base \ ⋃ k, D k) x) = M i) ∧
          ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M i,
            G.IsFinitePL ∧
            (∀ x, (G x : ℝ × ℝ) ∈ D i ↔ (x : ℝ × ℝ).2 = 0) ∧
            (∀ x, (G x : ℝ × ℝ) ∈ D (n i) ↔ (x : ℝ × ℝ).2 = 1) ∧
            (∀ x, (G x : ℝ × ℝ) ∈ cornerMap (c i) '' ({0} ×ˢ Icc (b i) (b (n i))) ↔
              (x : ℝ × ℝ).1 = 0) ∧
            (∀ x, (G x : ℝ × ℝ) ∈ cornerMap (c i) '' (Icc (a i) (a (n i)) ×ˢ {0}) ↔
              (x : ℝ × ℝ).1 = 1) := by
  classical
  obtain ⟨c, a, b, ha, hb, htype, _, hcard, hbound⟩ :=
    exists_normal_corner_order D p q hD hrim hdis hpv hqv hleft hbottom hdiagonal
  let Good := {i : ι // ∃ j, c j = c i ∧ a i < a j}
  have hex (i : Good) := exists_next_original_corner_rectangle D p q hD hsub hrim hdis
    hleft hbottom hdiagonal (c i) i (ha i) (hb i) (htype i) (by
      obtain ⟨j, hjc, hij⟩ := i.property
      exact ⟨j, a j, ha j, b j, hb j, hjc ▸ htype j, hij⟩)
  choose n u hu v hv hne hn hlt M hM hMB hother hcomponent G hG hGW hGZ hGL hGR using hex
  have hnc (i : Good) : c (n i) = c i :=
    corner_pair_unique (ha (n i)) (hb (n i)) (htype (n i)) (hn i)
  have hparams (i : Good) : a (n i) = u i ∧ b (n i) = v i := by
    have he := htype (n i)
    rw [hnc i] at he
    exact origin_pair_parameters_eq (ha (n i)).1 (hb (n i)).1 (he.symm.trans (hn i))
  have hless (i : Good) : a i < a (n i) := (hparams i).1.symm ▸ hlt i
  have hcontains (i : Good) : D i ⊆ M i := fun x hx => (hM i).1 (Or.inl hx)
  have hMi : Function.Injective M := by
    intro i j he
    apply Subtype.ext
    by_contra hneij
    have hi : (i : ι) = n j := by
      by_contra hnij
      obtain ⟨x, hx⟩ := (hD i).isConnected.nonempty
      exact disjoint_left.mp (hother j i hneij hnij) hx (he ▸ hcontains i hx)
    have hj : (j : ι) = n i := by
      by_contra hnji
      obtain ⟨x, hx⟩ := (hD j).isConnected.nonempty
      exact disjoint_left.mp (hother i j (fun he => hneij he.symm) hnji) hx (he.symm ▸ hcontains j hx)
    have hij := hless i
    have hji := hless j
    rw [← hj] at hij
    rw [← hi] at hji
    exact lt_asymm hij hji
  refine ⟨c, a, b, ha, hb, htype, hcard, hbound, n, M, hMi, ?_⟩
  intro i
  refine ⟨hnc i, hless i, ?_, ?_, hother i, hcomponent i, G i, hG i, hGW i, hGZ i, ?_, ?_⟩
  · simpa only [(hparams i).1, (hparams i).2] using hM i
  · simpa only [(hparams i).1, (hparams i).2] using hMB i
  · simpa only [(hparams i).2] using hGL i
  · simpa only [(hparams i).1] using hGR i

end PoincareConjecture.M76.TriangleCorner
