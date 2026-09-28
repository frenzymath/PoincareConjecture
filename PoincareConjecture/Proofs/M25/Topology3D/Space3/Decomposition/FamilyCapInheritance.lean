import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.EventCapInheritance

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_reindexed_surgery_cap_family
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (u : UnitTwoSphere) (j : Fin n)
    (E : RegularSurgeryEvent (psi j) u)
    (e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2))
    (m : ℕ) (owner : Fin m → Fin n)
    (C : (a : Fin m) → SurgeryCapTag (psi (owner a)) u)
    (havoid : ∀ a : Fin m, ∀ y ∈ (C a).cap,
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|)
    (hdisjoint : Pairwise (fun a b : Fin m =>
      Disjoint (C a).cap (C b).cap)) :
    let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
      fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
    ∃ owner' : (Fin m ⊕ Fin 2) → Fin (n + 1),
      ∃ D : (a : Fin m ⊕ Fin 2) → SurgeryCapTag (psi' (owner' a)) u,
        (∀ a : Fin m,
          (D (Sum.inl a)).profile = (C a).profile ∧
          (D (Sum.inl a)).tube = (C a).tube ∧
          (D (Sum.inl a)).cutHeight = (C a).cutHeight ∧
          (D (Sum.inl a)).removal = (C a).removal ∧
          (D (Sum.inl a)).scale = (C a).scale ∧
          (D (Sum.inl a)).sign = (C a).sign ∧
          (D (Sum.inl a)).cap = (C a).cap ∧
          (D (Sum.inl a)).seam = (C a).seam) ∧
        (∀ (a : Fin m) (h : owner a ≠ j),
          owner' (Sum.inl a) = e.symm (Sum.inl ⟨owner a, h⟩) ∧
          HEq (D (Sum.inl a)) (C a)) ∧
        (∀ a : Fin m, owner a = j →
          ∃ i : Fin 2,
            owner' (Sum.inl a) = e.symm (Sum.inr i) ∧
            (C a).sourceCap ⊆
              (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
                closedBall (0 : E2) E.radius ∧
            (∀ k : Fin 2, (C a).sourceCap ⊆
              (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] k) ''
                closedBall (0 : E2) E.radius → k = i) ∧
            (D (Sum.inl a)).sourceChart =
              (C a).sourceChart.trans (E.retainedChart i).symm ∧
            (D (Sum.inl a)).flatChart =
              (C a).flatChart.trans (E.retainedChart i).symm ∧
            (D (Sum.inl a)).beta = (C a).beta * E.retainedTime i ∧
            (D (Sum.inl a)).overlapWidth ≤ (C a).overlapWidth ∧
            (D (Sum.inl a)).collarWidth =
              min 1 ((C a).collarWidth / (|E.retainedTime i| + 1))) ∧
        (∀ i : Fin 2,
          owner' (Sum.inr i) = e.symm (Sum.inr i) ∧
          HEq (D (Sum.inr i)) (E.newCap i)) ∧
        Pairwise (fun a b : Fin m ⊕ Fin 2 => Disjoint (D a).cap (D b).cap) ∧
        (⋃ a : Fin m ⊕ Fin 2, (D a).cap) =
          (⋃ a : Fin m, (C a).cap) ∪ ((E.newCap 0).cap ∪ (E.newCap 1).cap) := by
  classical
  let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
    fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
  have holdMap (i : {i : Fin n // i ≠ j}) :
      psi' (e.symm (Sum.inl i)) = psi i.1 := by
    simp [psi']
  have hchildMap (i : Fin 2) :
      psi' (e.symm (Sum.inr i)) = E.child i := by
    simp [psi']
  let OldSpec (a : Fin m) (b : Fin (n + 1))
      (N : SurgeryCapTag (psi' b) u) : Prop :=
    (N.profile = (C a).profile ∧
      N.tube = (C a).tube ∧
      N.cutHeight = (C a).cutHeight ∧
      N.removal = (C a).removal ∧
      N.scale = (C a).scale ∧
      N.sign = (C a).sign ∧
      N.cap = (C a).cap ∧
      N.seam = (C a).seam) ∧
    (∀ h : owner a ≠ j,
      b = e.symm (Sum.inl ⟨owner a, h⟩) ∧ HEq N (C a)) ∧
    (owner a = j → ∃ i : Fin 2,
      b = e.symm (Sum.inr i) ∧
      (C a).sourceCap ⊆
        (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
          closedBall (0 : E2) E.radius ∧
      (∀ k : Fin 2, (C a).sourceCap ⊆
        (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] k) ''
          closedBall (0 : E2) E.radius → k = i) ∧
      N.sourceChart = (C a).sourceChart.trans (E.retainedChart i).symm ∧
      N.flatChart = (C a).flatChart.trans (E.retainedChart i).symm ∧
      N.beta = (C a).beta * E.retainedTime i ∧
      N.overlapWidth ≤ (C a).overlapWidth ∧
      N.collarWidth = min 1 ((C a).collarWidth / (|E.retainedTime i| + 1)))
  have hold (a : Fin m) :
      ∃ b : Fin (n + 1), ∃ N : SurgeryCapTag (psi' b) u, OldSpec a b N := by
    by_cases ha : owner a = j
    · subst j
      obtain ⟨i, N, hplace, hunique, hprofile, htube, hcut, hremoval,
        hscale, hsign, hsource, hflat, hbeta, hoverlap, hwidth, hcap, hseam⟩ :=
          E.exists_inherited_cap (C a) (havoid a)
      refine ⟨e.symm (Sum.inr i), ?_⟩
      dsimp only [OldSpec]
      rw [hchildMap i]
      refine ⟨N, ⟨hprofile, htube, hcut, hremoval, hscale, hsign, hcap, hseam⟩,
        ?_, ?_⟩
      · intro hne
        exact False.elim (hne rfl)
      · intro _
        exact ⟨i, rfl, hplace, hunique, hsource, hflat, hbeta, hoverlap, hwidth⟩
    · refine ⟨e.symm (Sum.inl ⟨owner a, ha⟩), ?_⟩
      dsimp only [OldSpec]
      rw [holdMap ⟨owner a, ha⟩]
      refine ⟨C a, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · intro _hne
        exact ⟨rfl, HEq.rfl⟩
      · intro heq
        exact False.elim (ha heq)
  choose oldOwner oldTag hOldSpec using hold
  have hnew (i : Fin 2) :
      ∃ N : SurgeryCapTag (psi' (e.symm (Sum.inr i))) u,
        HEq N (E.newCap i) ∧ N.cap = (E.newCap i).cap := by
    rw [hchildMap i]
    exact ⟨E.newCap i, HEq.rfl, rfl⟩
  choose newTag hNewHEq hNewCap using hnew
  let owner' : Fin m ⊕ Fin 2 → Fin (n + 1) :=
    Sum.elim oldOwner (fun i => e.symm (Sum.inr i))
  let D : (a : Fin m ⊕ Fin 2) → SurgeryCapTag (psi' (owner' a)) u :=
    fun a => match a with
      | Sum.inl b => oldTag b
      | Sum.inr i => newTag i
  have hOldCap (a : Fin m) : (D (Sum.inl a)).cap = (C a).cap := by
    obtain ⟨_, _, _, _, _, _, hcap, _⟩ := (hOldSpec a).1
    exact hcap
  have hNewCap' (i : Fin 2) : (D (Sum.inr i)).cap = (E.newCap i).cap :=
    hNewCap i
  have hOldNew (a : Fin m) (i : Fin 2) : Disjoint (C a).cap (E.newCap i).cap := by
    obtain ⟨_, _, hck, hkw, _, _⟩ := E.parameter_bounds
    obtain ⟨_, _, hcut, hremoval, _, _⟩ := E.newCap_spec i
    apply (C a).cap_disjoint_of_height_avoidance (E.newCap i) E.data.width
    · rw [hremoval]
      exact hck.trans hkw
    · intro y hy
      rw [hcut]
      exact havoid a y hy
  have hNewNew : Disjoint (E.newCap 0).cap (E.newCap 1).cap := by
    obtain ⟨_, _, _, _, _, hchildren⟩ := E.region_identities
    have hsub (i : Fin 2) : (E.newCap i).cap ⊆
        E.child i '' (univ ×ˢ ({0} : Set ℝ)) := by
      rintro y ⟨q, _hq, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    exact hchildren.mono (hsub 0) (hsub 1)
  refine ⟨owner', D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hOldSpec a).1
  · intro a h
    exact (hOldSpec a).2.1 h
  · intro a h
    exact (hOldSpec a).2.2 h
  · intro i
    exact ⟨rfl, hNewHEq i⟩
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · rw [hOldCap a, hOldCap b]
      exact hdisjoint (fun h => hab (congrArg Sum.inl h))
    · rw [hOldCap a, hNewCap' b]
      exact hOldNew a b
    · rw [hNewCap' a, hOldCap b]
      exact (hOldNew b a).symm
    · rw [hNewCap' a, hNewCap' b]
      fin_cases a <;> fin_cases b
      · exact False.elim (hab rfl)
      · exact hNewNew
      · exact hNewNew.symm
      · exact False.elim (hab rfl)
  · ext y
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      rcases a with a | i
      · rw [hOldCap a] at ha
        exact Or.inl (mem_iUnion.mpr ⟨a, ha⟩)
      · rw [hNewCap' i] at ha
        fin_cases i
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha)
    · rintro (hy | hy | hy)
      · obtain ⟨a, ha⟩ := mem_iUnion.mp hy
        refine mem_iUnion.mpr ⟨Sum.inl a, ?_⟩
        rw [hOldCap a]
        exact ha
      · refine mem_iUnion.mpr ⟨Sum.inr 0, ?_⟩
        rw [hNewCap' 0]
        exact hy
      · refine mem_iUnion.mpr ⟨Sum.inr 1, ?_⟩
        rw [hNewCap' 1]
        exact hy

theorem SurgeryCapTag.cap_avoids_separated_cuts
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u)
    (r : ℕ) (cut : Fin r → ℝ) (d : ℝ) (hd : 0 < d)
    (hsep : Pairwise (fun a b : Fin r =>
      Disjoint (Icc (cut a - d) (cut a + d))
        (Icc (cut b - d) (cut b + d))))
    (j : Fin r) (hcut : C.cutHeight = cut j) (hremoval : C.removal < d) :
    ∀ a : Fin r, ∀ y ∈ C.cap, ⟪(u : E3), y⟫_ℝ ≠ cut a := by
  intro a y hy heq
  have hbounds := C.cap_abs_height_bounds y hy
  by_cases haj : a = j
  · subst a
    simp only [heq, hcut, sub_self, abs_zero] at hbounds
    linarith [C.removal_pos, hbounds.1]
  · have habs : |⟪(u : E3), y⟫_ℝ - cut j| ≤ d := by
      rw [← hcut]
      exact hbounds.2.trans hremoval.le
    have hj : ⟪(u : E3), y⟫_ℝ ∈ Icc (cut j - d) (cut j + d) := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp habs
      constructor <;> linarith
    have ha : ⟪(u : E3), y⟫_ℝ ∈ Icc (cut a - d) (cut a + d) := by
      rw [heq]
      exact ⟨sub_le_self _ hd.le, le_add_of_nonneg_right hd.le⟩
    exact disjoint_left.mp (hsep (Ne.symm haj)) hj ha

end PoincareConjecture.M25.Topology3D
