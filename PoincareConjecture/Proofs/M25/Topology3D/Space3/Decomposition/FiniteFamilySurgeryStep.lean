import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryReindex
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySurgeryEvent
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyInnermostTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyLevelDeletion










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_finite_family_surgery_step
    (hP : PlanarSchoenfliesService) (P : SurgeryCapProfile)
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (u : UnitTwoSphere) (t d : ℝ) (hd : 0 < d)
    (m : ℕ) (hm : 0 < m) (B : Fin m → BallNeighborhoodChart E2 E2)
    (hB : Pairwise (fun i j : Fin m => Disjoint (B i).boundary (B j).boundary))
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hinverse : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2))
    (hlevel : ∀ z ∈ Ioo (t - d) (t + d), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈
        (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
          p ∈ (⋃ i : Fin m, (B i).boundary))
    (K : Set E3) (hK : IsCompact K)
    (hmiss : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ t) :
    ∃ k : Fin m, ∃ j : Fin n, ∃ E : RegularSurgeryEvent (psi j) u,
      ∃ e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2),
        ∃ remaining : Fin (m - 1) ≃ {i : Fin m // i ≠ k},
          let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
            fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1)
              E.child (e a)
          let c := E.data.width / 2 * (1 - E.radius)
          E.cutHeight = t ∧ E.data.width < d ∧
          E.data.tube = horizontalTubeChart Phi hPhi hinverse u (B k) ∧
          E.profile = P ∧
          (B k).closedRegion ∩ (⋃ i : Fin m, (B i).boundary) = (B k).boundary ∧
          (∀ y ∈ K, E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|) ∧
          0 < c / 2 ∧ c / 2 < E.data.width ∧ m - 1 < m ∧
          (∀ a : Fin (n + 1), IsCollarEmbedding (psi' a)) ∧
          Pairwise (fun a b : Fin (n + 1) =>
            Disjoint (range (fun q : UnitTwoSphere => psi' a (q, 0)))
              (range (fun q : UnitTwoSphere => psi' b (q, 0)))) ∧
          (∀ i : {i : Fin n // i ≠ j}, psi' (e.symm (Sum.inl i)) = psi i.1) ∧
          (∀ i : Fin 2, psi' (e.symm (Sum.inr i)) = E.child i) ∧
          Pairwise (fun a b : Fin (m - 1) =>
            Disjoint (B (remaining a).1).boundary (B (remaining b).1).boundary) ∧
          (∀ z ∈ Ioo (t - c / 2) (t + c / 2), ∀ p : E2,
            (heightPlaneCoordinates u).symm (Phi z p, z) ∈
              (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))) ↔
                p ∈ (⋃ a : Fin (m - 1), (B (remaining a).1).boundary)) ∧
          (∀ y : E3, E.data.width ≤ |⟪(u : E3), y⟫_ℝ - t| →
            (y ∈ (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))) ↔
              y ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))))) := by
  classical
  let old := ⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))
  obtain ⟨k, hinner, hsource, hsmooth, hinv, hheight, hwhole⟩ :=
    exists_innermost_family_tube old u t d hd m hm B hB Phi hPhi hinverse hlevel
  obtain ⟨j, E, hcut, hwidth, htube, hprofile, hprotected, hothers⟩ :=
    exists_family_surgery_event_avoiding hP P n psi hembed hdisjoint u t d hd
      (horizontalTubeChart Phi hPhi hinverse u (B k))
      hsource hsmooth hinv hheight hwhole K hK hmiss
  obtain ⟨e, hembed', hdisjoint', holdmap, hchildmap, hcover⟩ :=
    exists_family_surgery_reindex n psi hembed hdisjoint u j E hothers
  let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
    fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
  let new := ⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))
  let R := ⋃ i : {i : Fin n // i ≠ j},
    range (fun q : UnitTwoSphere => psi i.1 (q, 0))
  let c := E.data.width / 2 * (1 - E.radius)
  have hzero (g : UnitTwoSphere × ℝ → E3) :
      g '' (univ ×ˢ ({0} : Set ℝ)) = range (fun q : UnitTwoSphere => g (q, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hold : old = (psi j '' (univ ×ˢ ({0} : Set ℝ))) ∪ R := by
    rw [hzero]
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
    · rintro (hy | hy)
      · exact mem_iUnion.mpr ⟨j, hy⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact mem_iUnion.mpr ⟨i.1, hi⟩
  have hR : Disjoint R (psi j '' (univ ×ˢ ({0} : Set ℝ))) := by
    rw [hzero]
    apply disjoint_iUnion_left.mpr
    intro i
    exact hdisjoint i.2
  have hnew : new = ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
      (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∪ R := by
    rw [hzero, hzero]
    exact hcover.trans (union_comm _ _)
  have hlevel' : ∀ z ∈ Ioo (E.cutHeight - E.data.width)
      (E.cutHeight + E.data.width), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈
        (psi j '' (univ ×ˢ ({0} : Set ℝ))) ∪ R ↔
          p ∈ (⋃ i : Fin m, (B i).boundary) := by
    intro z hz p
    have hz' : z ∈ Ioo (t - d) (t + d) :=
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [← hold]
    exact hlevel z hz' p
  have hdelete := E.family_horizontal_levels_delete R hR m B hB k Phi
    hPhi hinverse htube hlevel'
  change ∀ z ∈ Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2), ∀ p : E2,
    (heightPlaneCoordinates u).symm (Phi z p, z) ∈
      ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
        (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∪ R ↔
          p ∈ (⋃ i : {i : Fin m // i ≠ k}, (B i.1).boundary) at hdelete
  rw [hcut, ← hnew] at hdelete
  have hcard : Fintype.card {i : Fin m // i ≠ k} = m - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin m => i = k)
  let remaining : Fin (m - 1) ≃ {i : Fin m // i ≠ k} :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hlabels : (⋃ i : {i : Fin m // i ≠ k}, (B i.1).boundary) =
      (⋃ a : Fin (m - 1), (B (remaining a).1).boundary) := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      refine mem_iUnion.mpr ⟨remaining.symm i, ?_⟩
      simpa only [remaining.apply_symm_apply] using hi
    · intro hp
      obtain ⟨a, ha⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨remaining a, ha⟩
  have hremaining : Pairwise (fun a b : Fin (m - 1) =>
      Disjoint (B (remaining a).1).boundary (B (remaining b).1).boundary) := by
    intro a b hab
    apply hB
    intro h
    exact hab (remaining.injective (Subtype.ext h))
  obtain ⟨_hd, hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  change 0 < c at hc
  have hcw : c < E.data.width := hck.trans hkw
  refine ⟨k, j, E, e, remaining, hcut, hwidth, htube, hprofile, hinner,
    hprotected, ?_, ?_, by omega, hembed', hdisjoint',
    holdmap, hchildmap, hremaining, ?_, ?_⟩
  · change 0 < c / 2
    exact half_pos hc
  · change c / 2 < E.data.width
    linarith
  · intro z hz p
    rw [← hlabels]
    exact hdelete z hz p
  · intro y hy
    change y ∈ new ↔ y ∈ old
    rw [hnew, hold]
    have hyW : E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight| := by
      calc
        E.data.width ≤ |⟪(u : E3), y⟫_ℝ - t| := hy
        _ = |⟪(u : E3), y⟫_ℝ - E.cutHeight| := by rw [hcut]
    have hout := E.children_outside_band
    constructor
    · rintro (hyChild | hyR)
      · exact Or.inl (((Set.ext_iff.mp hout y).mp ⟨hyChild, hyW⟩).1)
      · exact Or.inr hyR
    · rintro (hyParent | hyR)
      · exact Or.inl (((Set.ext_iff.mp hout y).mpr ⟨hyParent, hyW⟩).1)
      · exact Or.inr hyR

end PoincareConjecture.M25.Topology3D
