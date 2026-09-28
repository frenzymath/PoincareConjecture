import PoincareConjecture.Proofs.M02.SimplexCoherence
import PoincareConjecture.Proofs.M02.CubePrescribedNullhomotopy
import PoincareConjecture.Proofs.M02.SingularCycles

set_option autoImplicit false

universe w

open Set Topology CategoryTheory
open scoped unitInterval Simplicial

namespace PoincareConjecture.Proofs.M02

theorem exists_coherent_singularSimplex_boundary_nullhomotopy
    (X : TopCat.{w}) (x : X) (N : ℕ)
    (H : ∀ (k : ℕ) (_hk : k ≤ N) (s : (TopCat.toSSet.obj X) _⦋k⦌),
      (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x))
    (hcoh : ∀ (k : ℕ) (hk : k + 1 ≤ N)
      (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2))
      (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
      H (k + 1) hk s (t, stdSimplex.map i.succAbove z) =
        H k (Nat.le_trans (Nat.le_succ k) hk) ((TopCat.toSSet.obj X).δ i s) (t, z))
    (s : (TopCat.toSSet.obj X) _⦋N + 1⦌) :
    ∃ hb : C(unitInterval × {y : stdSimplex ℝ (Fin (N + 2)) // ∃ i, y i = 0}, X),
      (∀ y, hb (0, y) = X.toSSetObjEquiv _ s y.val) ∧
      (∀ y, hb (1, y) = x) ∧
      ∀ (i : Fin (N + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (N + 1)))
        (y : {y : stdSimplex ℝ (Fin (N + 2)) // ∃ i, y i = 0}),
        y.val = stdSimplex.map i.succAbove z →
          hb (t, y) = H N (Nat.le_refl N) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
  let h (i : Fin (N + 2)) : C(unitInterval × stdSimplex ℝ (Fin (N + 1)), X) :=
    (H N (Nat.le_refl N) ((TopCat.toSSet.obj X).δ i s)).toContinuousMap
  have hcompat : ∀ i j z w t,
      stdSimplex.map i.succAbove z = stdSimplex.map j.succAbove w →
        h i (t, z) = h j (t, w) := by
    cases N with
    | zero => exact stdSimplex_interval_face_homotopies_agree h
    | succ n =>
      apply stdSimplex_face_homotopies_agree_of_double_faces n h
      intro i j t z
      change H (n + 1) _ ((TopCat.toSSet.obj X).δ i s)
          (t, stdSimplex.map j.succAbove z) =
        H (n + 1) _ ((TopCat.toSSet.obj X).δ (i.succAbove j) s)
          (t, stdSimplex.map (j.predAbove i).succAbove z)
      rw [hcoh n (Nat.le_refl _), hcoh n (Nat.le_refl _), singularSimplex_double_face]
  obtain ⟨q, hq, hqface⟩ := exists_stdSimplex_boundary_face_quotient N
  obtain ⟨hb, htrace, _⟩ :=
    existsUnique_stdSimplex_boundary_face_homotopy N q hq hqface h hcompat
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨⟨i, z⟩, rfl⟩ := hq.surjective y
    rw [htrace]
    change H N _ ((TopCat.toSSet.obj X).δ i s) (0, z) =
      X.toSSetObjEquiv _ s (q ⟨i, z⟩).val
    rw [ContinuousMap.Homotopy.apply_zero, TopCat.toSSetObjEquiv_δ_apply, hqface]
  · intro y
    obtain ⟨⟨i, z⟩, rfl⟩ := hq.surjective y
    exact (htrace 1 i z).trans ((H N _ ((TopCat.toSSet.obj X).δ i s)).apply_one z)
  · intro i t z y hy
    have hyq : y = q ⟨i, z⟩ := Subtype.ext (hy.trans (hqface i z).symm)
    subst y
    exact htrace t i z

theorem exists_coherent_singularSimplex_nullhomotopies
    (X : TopCat.{w}) [PathConnectedSpace X] (x : X) (N : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ N → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ H : ∀ (k : ℕ) (_hk : k ≤ N) (s : (TopCat.toSSet.obj X) _⦋k⦌),
      (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x),
      ∀ (k : ℕ) (hk : k + 1 ≤ N)
        (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2))
        (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        H (k + 1) hk s (t, stdSimplex.map i.succAbove z) =
          H k (Nat.le_trans (Nat.le_succ k) hk) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
  classical
  induction N with
  | zero =>
    have H0 (s : (TopCat.toSSet.obj X) _⦋0⦌) :
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x) := by
      let z0 : stdSimplex ℝ (Fin 1) := default
      let p := PathConnectedSpace.somePath (X.toSSetObjEquiv _ s z0) x
      exact {
        toFun := fun u => p u.1
        continuous_toFun := p.continuous.comp continuous_fst
        map_zero_left := fun z => p.source.trans
          (congrArg (X.toSSetObjEquiv _ s) (Subsingleton.elim z0 z))
        map_one_left := fun _ => p.target
      }
    refine ⟨?_, ?_⟩
    · intro k hk s
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact H0 s
    · intro k hk
      exact (Nat.not_succ_le_zero k hk).elim
  | succ N ih =>
    obtain ⟨H, hcoh⟩ := ih (fun k hk hkN => hpi k hk (Nat.le_trans hkN (Nat.le_succ N)))
    have hext (s : (TopCat.toSSet.obj X) _⦋N + 1⦌) :
        ∃ G : (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x),
          ∀ (i : Fin (N + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (N + 1))),
            G (t, stdSimplex.map i.succAbove z) =
              H N (Nat.le_refl N) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
      obtain ⟨hb, hb0, hb1, hbf⟩ :=
        exists_coherent_singularSimplex_boundary_nullhomotopy X x N H hcoh s
      obtain ⟨G, hG⟩ := exists_stdSimplex_nullhomotopy_with_prescribed_boundary N x
        (hpi (N + 1) (Nat.succ_le_succ (Nat.zero_le N)) (Nat.le_refl _))
        (X.toSSetObjEquiv _ s) hb hb0 hb1
      refine ⟨G, fun i t z => ?_⟩
      have hz : stdSimplex.map i.succAbove z i = 0 := by
        have hz' : stdSimplex.map i.succAbove z ∈
            range (stdSimplex.map (S := ℝ) i.succAbove) := mem_range_self z
        rw [stdSimplex_face_map_range] at hz'
        exact hz'
      let y : {y : stdSimplex ℝ (Fin (N + 2)) // ∃ i, y i = 0} :=
        ⟨stdSimplex.map i.succAbove z, i, hz⟩
      exact (hG t y).trans (hbf i t z y rfl)
    choose G hG using hext
    let K (k : ℕ) (hk : k ≤ N + 1) (s : (TopCat.toSSet.obj X) _⦋k⦌) :
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x) :=
      if hkN : k ≤ N then H k hkN s else by
        have heq : k = N + 1 := by omega
        subst k
        exact G s
    refine ⟨K, ?_⟩
    intro k hk s i t z
    by_cases hkN : k + 1 ≤ N
    · have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hkN
      simpa only [K, dif_pos hkN, dif_pos hk'] using hcoh k hkN s i t z
    · have hk' : k = N := by omega
      subst k
      simpa only [K, dif_neg (Nat.not_succ_le_self N), dif_pos (Nat.le_refl N)] using hG s i t z

theorem exists_singularSimplex_straightening
    (X : TopCat.{w}) [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ (K : ∀ (k : ℕ) (_hk : k ≤ n) (s : (TopCat.toSSet.obj X) _⦋k⦌),
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x))
      (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
      (H : ∀ s, (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ (r s))),
      (∀ (k : ℕ) (hk : k + 1 ≤ n)
        (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2))
        (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        K (k + 1) hk s (t, stdSimplex.map i.succAbove z) =
          K k (Nat.le_trans (Nat.le_succ k) hk) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
      (∀ s (i : Fin (n + 2)),
        (TopCat.toSSet.obj X).δ i (r s) = singularConstantSimplex X n x) ∧
      ∀ s (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
        H s (t, stdSimplex.map i.succAbove z) =
          K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
  classical
  obtain ⟨K, hcoh⟩ := exists_coherent_singularSimplex_nullhomotopies X x n hpi
  have hext (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
      ∃ (r : (TopCat.toSSet.obj X) _⦋n + 1⦌)
        (H : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r)),
        (∀ i : Fin (n + 2), (TopCat.toSSet.obj X).δ i r = singularConstantSimplex X n x) ∧
        ∀ (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
          H (t, stdSimplex.map i.succAbove z) =
            K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
    obtain ⟨hb, hb0, _hb1, hbf⟩ :=
      exists_coherent_singularSimplex_boundary_nullhomotopy X x n K hcoh s
    obtain ⟨F, hF0, hFB⟩ :=
      exists_stdSimplex_homotopy_extension (n + 1) (X.toSSetObjEquiv _ s) hb hb0
    let f1 : C(stdSimplex ℝ (Fin (n + 2)), X) :=
      ⟨fun z => F (1, z), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    let r : (TopCat.toSSet.obj X) _⦋n + 1⦌ :=
      (X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)).symm f1
    have hr : X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌) r = f1 :=
      (X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)).apply_symm_apply f1
    let H : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r) := {
      toContinuousMap := F
      map_zero_left := hF0
      map_one_left := fun z => (DFunLike.congr_fun hr z).symm
    }
    have htrace (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))) :
        H (t, stdSimplex.map i.succAbove z) =
          K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
      have hz : stdSimplex.map i.succAbove z i = 0 := by
        have hz' : stdSimplex.map i.succAbove z ∈
            range (stdSimplex.map (S := ℝ) i.succAbove) := mem_range_self z
        rw [stdSimplex_face_map_range] at hz'
        exact hz'
      let y : {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0} :=
        ⟨stdSimplex.map i.succAbove z, i, hz⟩
      exact (hFB t y).trans (hbf i t z y rfl)
    refine ⟨r, H, ?_, htrace⟩
    intro i
    apply (X.toSSetObjEquiv _).injective
    ext z
    simp only [TopCat.toSSetObjEquiv_δ_apply, singularConstantSimplex,
      Equiv.apply_symm_apply, ContinuousMap.const_apply]
    exact (H.apply_one (stdSimplex.map i.succAbove z)).symm.trans
      ((htrace i 1 z).trans ((K n _ ((TopCat.toSSet.obj X).δ i s)).apply_one z))
  choose r H hr htrace using hext
  exact ⟨K, r, H, hcoh, hr, htrace⟩

theorem exists_normalized_coherent_singularSimplex_nullhomotopies
    (X : TopCat.{w}) [PathConnectedSpace X] (x : X) (N : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ N → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ H : ∀ (k : ℕ) (_hk : k ≤ N) (s : (TopCat.toSSet.obj X) _⦋k⦌),
      (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x),
      (∀ (k : ℕ) (hk : k + 1 ≤ N)
        (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2))
        (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        H (k + 1) hk s (t, stdSimplex.map i.succAbove z) =
          H k (Nat.le_trans (Nat.le_succ k) hk) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
      ∀ (k : ℕ) (hk : k ≤ N) (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        H k hk (singularConstantSimplex X k x) (t, z) = x := by
  classical
  induction N with
  | zero =>
    obtain ⟨H, _hcoh⟩ := exists_coherent_singularSimplex_nullhomotopies X x 0 hpi
    have hzero (s : (TopCat.toSSet.obj X) _⦋0⦌) :
        ∃ G : (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x),
          s = singularConstantSimplex X 0 x →
            ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin 1)), G (t, z) = x := by
      by_cases hs : s = singularConstantSimplex X 0 x
      · subst s
        let G : (X.toSSetObjEquiv _ (singularConstantSimplex X 0 x)).Homotopy
            (ContinuousMap.const _ x) :=
          (ContinuousMap.Homotopy.refl (ContinuousMap.const _ x)).cast
            (by simp only [singularConstantSimplex, Equiv.apply_symm_apply]) rfl
        exact ⟨G, fun _ _ _ => rfl⟩
      · exact ⟨H 0 (Nat.le_refl 0) s, fun hs' => (hs hs').elim⟩
    choose H0 hH0 using hzero
    let K (k : ℕ) (hk : k ≤ 0) (s : (TopCat.toSSet.obj X) _⦋k⦌) :
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x) := by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact H0 s
    refine ⟨K, ?_, ?_⟩
    · intro k hk
      exact (Nat.not_succ_le_zero k hk).elim
    · intro k hk t z
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hH0 (singularConstantSimplex X 0 x) rfl t z
  | succ N ih =>
    obtain ⟨H, hcoh, hconst⟩ :=
      ih (fun k hk hkN => hpi k hk (Nat.le_trans hkN (Nat.le_succ N)))
    have hext (s : (TopCat.toSSet.obj X) _⦋N + 1⦌) :
        ∃ G : (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x),
          (∀ (i : Fin (N + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (N + 1))),
            G (t, stdSimplex.map i.succAbove z) =
              H N (Nat.le_refl N) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
          (s = singularConstantSimplex X (N + 1) x →
            ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin (N + 2))), G (t, z) = x) := by
      by_cases hs : s = singularConstantSimplex X (N + 1) x
      · subst s
        let G : (X.toSSetObjEquiv _ (singularConstantSimplex X (N + 1) x)).Homotopy
            (ContinuousMap.const _ x) :=
          (ContinuousMap.Homotopy.refl (ContinuousMap.const _ x)).cast
            (by simp only [singularConstantSimplex, Equiv.apply_symm_apply]) rfl
        refine ⟨G, ?_, fun _ _ _ => rfl⟩
        intro i t z
        change x = H N _ ((TopCat.toSSet.obj X).δ i
          (singularConstantSimplex X (N + 1) x)) (t, z)
        rw [singularConstantSimplex_face, hconst]
      · obtain ⟨hb, hb0, hb1, hbf⟩ :=
          exists_coherent_singularSimplex_boundary_nullhomotopy X x N H hcoh s
        obtain ⟨G, hG⟩ := exists_stdSimplex_nullhomotopy_with_prescribed_boundary N x
          (hpi (N + 1) (Nat.succ_le_succ (Nat.zero_le N)) (Nat.le_refl _))
          (X.toSSetObjEquiv _ s) hb hb0 hb1
        refine ⟨G, ?_, fun hs' => (hs hs').elim⟩
        intro i t z
        have hz : stdSimplex.map i.succAbove z i = 0 := by
          have hz' : stdSimplex.map i.succAbove z ∈
              range (stdSimplex.map (S := ℝ) i.succAbove) := mem_range_self z
          rw [stdSimplex_face_map_range] at hz'
          exact hz'
        let y : {y : stdSimplex ℝ (Fin (N + 2)) // ∃ i, y i = 0} :=
          ⟨stdSimplex.map i.succAbove z, i, hz⟩
        exact (hG t y).trans (hbf i t z y rfl)
    choose G hG hGconst using hext
    let K (k : ℕ) (hk : k ≤ N + 1) (s : (TopCat.toSSet.obj X) _⦋k⦌) :
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x) :=
      if hkN : k ≤ N then H k hkN s else by
        have heq : k = N + 1 := by omega
        subst k
        exact G s
    refine ⟨K, ?_, ?_⟩
    · intro k hk s i t z
      by_cases hkN : k + 1 ≤ N
      · have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hkN
        simpa only [K, dif_pos hkN, dif_pos hk'] using hcoh k hkN s i t z
      · have hk' : k = N := by omega
        subst k
        simpa only [K, dif_neg (Nat.not_succ_le_self N), dif_pos (Nat.le_refl N)] using
          hG s i t z
    · intro k hk t z
      by_cases hkN : k ≤ N
      · simpa only [K, dif_pos hkN] using hconst k hkN t z
      · have hk' : k = N + 1 := by omega
        subst k
        simpa only [K, dif_neg (Nat.not_succ_le_self N)] using
          hGconst (singularConstantSimplex X (N + 1) x) rfl t z

theorem exists_normalized_singularSimplex_straightening
    (X : TopCat.{w}) [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n → Subsingleton (HomotopyGroup.Pi k X x)) :
    ∃ (K : ∀ (k : ℕ) (_hk : k ≤ n) (s : (TopCat.toSSet.obj X) _⦋k⦌),
        (X.toSSetObjEquiv _ s).Homotopy (ContinuousMap.const _ x))
      (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
      (H : ∀ s, (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ (r s))),
      (∀ (k : ℕ) (hk : k + 1 ≤ n)
        (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2))
        (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        K (k + 1) hk s (t, stdSimplex.map i.succAbove z) =
          K k (Nat.le_trans (Nat.le_succ k) hk) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
      (∀ (k : ℕ) (hk : k ≤ n) (t : unitInterval) (z : stdSimplex ℝ (Fin (k + 1))),
        K k hk (singularConstantSimplex X k x) (t, z) = x) ∧
      (∀ s (i : Fin (n + 2)),
        (TopCat.toSSet.obj X).δ i (r s) = singularConstantSimplex X n x) ∧
      (∀ s (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
        H s (t, stdSimplex.map i.succAbove z) =
          K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
      ∀ s, (∀ i : Fin (n + 2),
        (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) →
          r s = s ∧ ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 2))),
            H s (t, z) = X.toSSetObjEquiv _ s z := by
  classical
  obtain ⟨K, hcoh, hconst⟩ :=
    exists_normalized_coherent_singularSimplex_nullhomotopies X x n hpi
  have hext (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
      ∃ (r : (TopCat.toSSet.obj X) _⦋n + 1⦌)
        (H : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r)),
        (∀ i : Fin (n + 2), (TopCat.toSSet.obj X).δ i r = singularConstantSimplex X n x) ∧
        (∀ (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
          H (t, stdSimplex.map i.succAbove z) =
            K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z)) ∧
        ((∀ i : Fin (n + 2), (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) →
          r = s ∧ ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 2))),
            H (t, z) = X.toSSetObjEquiv _ s z) := by
    by_cases hs : ∀ i : Fin (n + 2),
        (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x
    · refine ⟨s, ContinuousMap.Homotopy.refl (X.toSSetObjEquiv _ s), hs, ?_,
        fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      intro i t z
      change X.toSSetObjEquiv _ s (stdSimplex.map i.succAbove z) =
        K n _ ((TopCat.toSSet.obj X).δ i s) (t, z)
      rw [hs, hconst]
      have h := congrArg (fun u => X.toSSetObjEquiv (Opposite.op ⦋n⦌) u z) (hs i)
      simpa only [TopCat.toSSetObjEquiv_δ_apply, singularConstantSimplex,
        Equiv.apply_symm_apply, ContinuousMap.const_apply] using h
    · obtain ⟨hb, hb0, _hb1, hbf⟩ :=
        exists_coherent_singularSimplex_boundary_nullhomotopy X x n K hcoh s
      obtain ⟨F, hF0, hFB⟩ :=
        exists_stdSimplex_homotopy_extension (n + 1) (X.toSSetObjEquiv _ s) hb hb0
      let f1 : C(stdSimplex ℝ (Fin (n + 2)), X) :=
        ⟨fun z => F (1, z), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      let r : (TopCat.toSSet.obj X) _⦋n + 1⦌ :=
        (X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)).symm f1
      have hr : X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌) r = f1 :=
        (X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)).apply_symm_apply f1
      let H : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r) := {
        toContinuousMap := F
        map_zero_left := hF0
        map_one_left := fun z => (DFunLike.congr_fun hr z).symm
      }
      have htrace (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))) :
          H (t, stdSimplex.map i.succAbove z) =
            K n (Nat.le_refl n) ((TopCat.toSSet.obj X).δ i s) (t, z) := by
        have hz : stdSimplex.map i.succAbove z i = 0 := by
          have hz' : stdSimplex.map i.succAbove z ∈
              range (stdSimplex.map (S := ℝ) i.succAbove) := mem_range_self z
          rw [stdSimplex_face_map_range] at hz'
          exact hz'
        let y : {y : stdSimplex ℝ (Fin (n + 2)) // ∃ i, y i = 0} :=
          ⟨stdSimplex.map i.succAbove z, i, hz⟩
        exact (hFB t y).trans (hbf i t z y rfl)
      refine ⟨r, H, ?_, htrace, fun hs' => (hs hs').elim⟩
      intro i
      apply (X.toSSetObjEquiv _).injective
      ext z
      simp only [TopCat.toSSetObjEquiv_δ_apply, singularConstantSimplex,
        Equiv.apply_symm_apply, ContinuousMap.const_apply]
      exact (H.apply_one (stdSimplex.map i.succAbove z)).symm.trans
        ((htrace i 1 z).trans ((K n _ ((TopCat.toSSet.obj X).δ i s)).apply_one z))
  choose r H hr htrace hfix using hext
  exact ⟨K, r, H, hcoh, hconst, hr, htrace, hfix⟩

theorem exists_singularSimplex_straightening_extension
    (X : TopCat.{w}) (n : ℕ)
    (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (H : ∀ s, (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ (r s)))
    (K : (TopCat.toSSet.obj X) _⦋n⦌ → C(unitInterval × stdSimplex ℝ (Fin (n + 1)), X))
    (htrace : ∀ s (i : Fin (n + 2)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H s (t, stdSimplex.map i.succAbove z) = K ((TopCat.toSSet.obj X).δ i s) (t, z))
    (s : (TopCat.toSSet.obj X) _⦋n + 2⦌) :
    ∃ (r' : (TopCat.toSSet.obj X) _⦋n + 2⦌)
      (F : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r')),
      (∀ i : Fin (n + 3), (TopCat.toSSet.obj X).δ i r' = r ((TopCat.toSSet.obj X).δ i s)) ∧
      ∀ (i : Fin (n + 3)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 2))),
        F (t, stdSimplex.map i.succAbove z) = H ((TopCat.toSSet.obj X).δ i s) (t, z) := by
  let h (i : Fin (n + 3)) : C(unitInterval × stdSimplex ℝ (Fin (n + 2)), X) :=
    (H ((TopCat.toSSet.obj X).δ i s)).toContinuousMap
  have hcompat : ∀ i j z w t,
      stdSimplex.map i.succAbove z = stdSimplex.map j.succAbove w →
        h i (t, z) = h j (t, w) := by
    apply stdSimplex_face_homotopies_agree_of_double_faces n h
    intro i j t z
    change H ((TopCat.toSSet.obj X).δ i s) (t, stdSimplex.map j.succAbove z) =
      H ((TopCat.toSSet.obj X).δ (i.succAbove j) s)
        (t, stdSimplex.map (j.predAbove i).succAbove z)
    rw [htrace, htrace, singularSimplex_double_face]
  obtain ⟨q, hq, hqface⟩ := exists_stdSimplex_boundary_face_quotient (n + 1)
  obtain ⟨hb, hbf, _hunique⟩ :=
    existsUnique_stdSimplex_boundary_face_homotopy (n + 1) q hq hqface h hcompat
  have hb0 (y : {y : stdSimplex ℝ (Fin (n + 3)) // ∃ i, y i = 0}) :
      hb (0, y) = X.toSSetObjEquiv _ s y.val := by
    obtain ⟨⟨i, z⟩, rfl⟩ := hq.surjective y
    rw [hbf]
    change H ((TopCat.toSSet.obj X).δ i s) (0, z) =
      X.toSSetObjEquiv _ s (q ⟨i, z⟩).val
    rw [ContinuousMap.Homotopy.apply_zero, TopCat.toSSetObjEquiv_δ_apply, hqface]
  obtain ⟨G, hG0, hGB⟩ :=
    exists_stdSimplex_homotopy_extension (n + 2) (X.toSSetObjEquiv _ s) hb hb0
  let f1 : C(stdSimplex ℝ (Fin (n + 3)), X) :=
    ⟨fun z => G (1, z), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let r' : (TopCat.toSSet.obj X) _⦋n + 2⦌ :=
    (X.toSSetObjEquiv (Opposite.op ⦋n + 2⦌)).symm f1
  have hr' : X.toSSetObjEquiv (Opposite.op ⦋n + 2⦌) r' = f1 :=
    (X.toSSetObjEquiv (Opposite.op ⦋n + 2⦌)).apply_symm_apply f1
  let F : (X.toSSetObjEquiv _ s).Homotopy (X.toSSetObjEquiv _ r') := {
    toContinuousMap := G
    map_zero_left := hG0
    map_one_left := fun z => (DFunLike.congr_fun hr' z).symm
  }
  have hF (i : Fin (n + 3)) (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 2))) :
      F (t, stdSimplex.map i.succAbove z) = H ((TopCat.toSSet.obj X).δ i s) (t, z) := by
    change G (t, stdSimplex.map i.succAbove z) = h i (t, z)
    have heq := (hGB t (q ⟨i, z⟩)).trans (hbf t i z)
    simpa only [hqface] using heq
  refine ⟨r', F, ?_, hF⟩
  intro i
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  exact (F.apply_one (stdSimplex.map i.succAbove z)).symm.trans
    ((hF i 1 z).trans ((H ((TopCat.toSSet.obj X).δ i s)).apply_one z))

end PoincareConjecture.Proofs.M02
