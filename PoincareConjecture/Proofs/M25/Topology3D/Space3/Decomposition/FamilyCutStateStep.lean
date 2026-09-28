import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutState
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FiniteFamilySurgeryStep
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCapInheritance
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutPreservation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace BigOperators

namespace PoincareConjecture.M25.Topology3D

theorem FamilyCutState.exists_surgery_step
    (hP : PlanarSchoenfliesService)
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (k : Fin r) (hk : 0 < S.count k)
    (K : Set E3) (hK : IsCompact K)
    (hmiss : ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ cut k) :
    ∃ chosen : Fin (S.count k), ∃ j : Fin n,
      ∃ E : RegularSurgeryEvent (psi j) u,
        ∃ e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2),
          let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
            fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1)
              E.child (e a)
          let c := E.data.width / 2 * (1 - E.radius)
          E.cutHeight = cut k ∧ E.profile = P ∧ E.data.width < S.width k ∧
            E.data.tube = horizontalTubeChart (Phi k) (S.family_smooth k)
              (S.family_inverse k) u (B k (S.label k chosen)) ∧
            (∀ y ∈ K, E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|) ∧
            ∃ S' : FamilyCutState P u r cut D m0 B Phi (n + 1) psi',
              S'.count = Function.update S.count k (S.count k - 1) ∧
              S'.width = Function.update S.width k (c / 2) ∧
              S'.measure + 1 = S.measure ∧
              (range (S'.label k) = range (S.label k) \ {S.label k chosen}) ∧
              (∀ l : Fin r, l ≠ k → range (S'.label l) = range (S.label l)) ∧
              S'.capCount = S.capCount + 2 ∧
              ∃ gamma : Fin S'.capCount ≃ (Fin S.capCount ⊕ Fin 2),
                (∀ a : Fin S.capCount,
                  let b := gamma.symm (Sum.inl a)
                  S'.birth b = S.birth a ∧
                    (S'.cap b).profile = (S.cap a).profile ∧
                    (S'.cap b).tube = (S.cap a).tube ∧
                    (S'.cap b).cutHeight = (S.cap a).cutHeight ∧
                    (S'.cap b).removal = (S.cap a).removal ∧
                    (S'.cap b).scale = (S.cap a).scale ∧
                    (S'.cap b).sign = (S.cap a).sign ∧
                    (S'.cap b).cap = (S.cap a).cap ∧
                    (S'.cap b).seam = (S.cap a).seam) ∧
                (∀ i : Fin 2,
                  let b := gamma.symm (Sum.inr i)
                  S'.owner b = e.symm (Sum.inr i) ∧ S'.birth b = k ∧
                    HEq (S'.cap b) (E.newCap i)) ∧
                ((⋃ a : Fin S'.capCount, (S'.cap a).cap) =
                  (⋃ a : Fin S.capCount, (S.cap a).cap) ∪
                    ((E.newCap 0).cap ∪ (E.newCap 1).cap)) ∧
                ∀ y : E3, E.data.width ≤ |⟪(u : E3), y⟫_ℝ - cut k| →
                  (y ∈ (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))) ↔
                    y ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0)))) := by
  classical
  have hB : Pairwise (fun a b : Fin (S.count k) =>
      Disjoint (B k (S.label k a)).boundary (B k (S.label k b)).boundary) := by
    intro a b hab
    exact S.planar_disjoint k (fun h => hab ((S.label k).injective h))
  obtain ⟨chosen, j, E, e, remaining, hcut, hwidth, htube, hprofile,
      _hinner, hprotected, hcpos, hcw, _hdecrease, hembed, hdisjoint,
      _holdmap, hchildmap, _hdiscs, hselected, houter⟩ :=
    exists_finite_family_surgery_step hP P n psi S.embedding S.central_disjoint
      u (cut k) (S.width k) (S.width_pos k) (S.count k) hk
      (fun a => B k (S.label k a)) hB (Phi k) (S.family_smooth k)
      (S.family_inverse k) (S.level_eq k) K hK hmiss
  let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
    fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
  let c := E.data.width / 2 * (1 - E.radius)
  have hc : 0 < c := by change 0 < c / 2 at hcpos; linarith only [hcpos]
  have hwD : E.data.width ≤ D := hwidth.le.trans (S.width_le k)
  have hcD : c ≤ D := by
    obtain ⟨_, _, hck, hkw, _, _⟩ := E.parameter_bounds
    exact (hck.trans hkw).le.trans hwD
  let width' : Fin r → ℝ := Function.update S.width k (c / 2)
  have hwidthpos (l : Fin r) : 0 < width' l := by
    by_cases hl : l = k
    · subst l
      simpa only [width', Function.update_self] using hcpos
    · simpa only [width', Function.update_of_ne hl] using S.width_pos l
  have hwidthold (l : Fin r) : width' l ≤ S.width l := by
    by_cases hl : l = k
    · subst l
      simpa only [width', Function.update_self] using (hcw.trans hwidth).le
    · simp only [width', Function.update_of_ne hl, le_refl]
  let keep : Fin (S.count k - 1) ↪ Fin (m0 k) := {
    toFun := fun a => S.label k (remaining a).1
    inj' := fun a b hab => remaining.injective (Subtype.ext ((S.label k).injective hab)) }
  let oldPack : (l : Fin r) → Σ m : ℕ, Fin m ↪ Fin (m0 l) :=
    fun l => ⟨S.count l, S.label l⟩
  let packs := Function.update oldPack k ⟨S.count k - 1, keep⟩
  let count' : Fin r → ℕ := fun l => (packs l).1
  let label' : (l : Fin r) → Fin (count' l) ↪ Fin (m0 l) := fun l => (packs l).2
  have hpackk : packs k = ⟨S.count k - 1, keep⟩ := Function.update_self _ _ _
  have hpackother (l : Fin r) (hl : l ≠ k) : packs l = oldPack l :=
    Function.update_of_ne hl _ _
  have hcount : count' = Function.update S.count k (S.count k - 1) := by
    funext l
    by_cases hl : l = k
    · subst l
      simp only [count', packs, Function.update_self]
    · simp only [count', packs, Function.update_of_ne hl, oldPack]
  have hkeep : range keep = range (S.label k) \ {S.label k chosen} := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨(remaining a).1, rfl⟩, ?_⟩
      change S.label k (remaining a).1 ≠ S.label k chosen
      exact fun h => (remaining a).2 ((S.label k).injective h)
    · rintro ⟨⟨a, rfl⟩, ha⟩
      have hachosen : a ≠ chosen := by
        intro h
        apply ha
        change S.label k a = S.label k chosen
        rw [h]
      refine ⟨remaining.symm ⟨a, hachosen⟩, ?_⟩
      change S.label k (remaining (remaining.symm ⟨a, hachosen⟩)).1 = S.label k a
      rw [remaining.apply_symm_apply]
  have hlevel' : ∀ l : Fin r, ∀ z ∈ Ioo (cut l - width' l) (cut l + width' l),
      ∀ p : E2,
        (heightPlaneCoordinates u).symm (Phi l z p, z) ∈
          (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0))) ↔
            p ∈ (⋃ a : Fin (count' l), (B l (label' l a)).boundary) := by
    intro l
    by_cases hl : l = k
    · subst l
      have hU : (⋃ a : Fin (count' k), (B k (label' k a)).boundary) =
          (⋃ a : Fin (S.count k - 1), (B k (S.label k (remaining a).1)).boundary) :=
        congrArg (fun v : Σ m : ℕ, Fin m ↪ Fin (m0 k) =>
          ⋃ a : Fin v.1, (B k (v.2 a)).boundary) hpackk
      rw [hU]
      simpa only [width', Function.update_self] using hselected
    · have hother := family_levels_preserved_at_separated_cut
        (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0)))
        (⋃ a : Fin (n + 1), range (fun q : UnitTwoSphere => psi' a (q, 0)))
        u (cut k) (cut l) D (S.width l) E.data.width hwD (S.width_le l)
        (S.buffers_separated (Ne.symm hl)) houter (S.count l)
        (fun a => B l (S.label l a)) (Phi l) (S.level_eq l)
      have hU : (⋃ a : Fin (count' l), (B l (label' l a)).boundary) =
          (⋃ a : Fin (S.count l), (B l (S.label l a)).boundary) :=
        congrArg (fun v : Σ m : ℕ, Fin m ↪ Fin (m0 l) =>
          ⋃ a : Fin v.1, (B l (v.2 a)).boundary) (hpackother l hl)
      rw [hU]
      simpa only [width', Function.update_of_ne hl] using hother
  have havoid : ∀ a : Fin S.capCount, ∀ y ∈ (S.cap a).cap,
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight| := by
    intro a y hy
    calc
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - cut k| :=
        hwidth.le.trans (S.caps_avoid a k y hy)
      _ = |⟪(u : E3), y⟫_ℝ - E.cutHeight| := by rw [hcut]
  obtain ⟨ownerSum, tagSum, hold, _hotherowner, _hparentowner,
      hnew, hcapdisjoint, hcapunion⟩ :=
    exists_reindexed_surgery_cap_family n psi u j E e S.capCount
      S.owner S.cap havoid S.caps_disjoint
  let birthSum : Fin S.capCount ⊕ Fin 2 → Fin r := Sum.elim S.birth (fun _ => k)
  have hphysical {f g : UnitTwoSphere × ℝ → E3} (hfg : f = g)
      {C : SurgeryCapTag f u} {N : SurgeryCapTag g u} (hCN : HEq C N) :
      C.profile = N.profile ∧ C.cutHeight = N.cutHeight ∧
        C.removal = N.removal ∧ C.cap = N.cap := by
    subst g
    have h := eq_of_heq hCN
    subst N
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hnewphysical (i : Fin 2) :
      (tagSum (Sum.inr i)).profile = (E.newCap i).profile ∧
        (tagSum (Sum.inr i)).cutHeight = (E.newCap i).cutHeight ∧
        (tagSum (Sum.inr i)).removal = (E.newCap i).removal ∧
        (tagSum (Sum.inr i)).cap = (E.newCap i).cap := by
    apply hphysical ?_ (hnew i).2
    change psi' (ownerSum (Sum.inr i)) = E.child i
    rw [(hnew i).1]
    exact hchildmap i
  have htagprofile (a : Fin S.capCount ⊕ Fin 2) : (tagSum a).profile = P := by
    rcases a with a | i
    · exact (hold a).1.trans (S.cap_profile a)
    · exact (hnewphysical i).1.trans ((E.newCap_spec i).1.trans hprofile)
  have htagcut (a : Fin S.capCount ⊕ Fin 2) :
      (tagSum a).cutHeight = cut (birthSum a) := by
    rcases a with a | i
    · exact (hold a).2.2.1.trans (S.cap_cut a)
    · exact (hnewphysical i).2.1.trans ((E.newCap_spec i).2.2.1.trans hcut)
  have htagremoval (a : Fin S.capCount ⊕ Fin 2) : (tagSum a).removal ≤ D := by
    rcases a with a | i
    · rw [(hold a).2.2.2.1]
      exact S.cap_removal a
    · rw [(hnewphysical i).2.2.1, (E.newCap_spec i).2.2.2.1]
      exact hcD
  have htagavoid (a : Fin S.capCount ⊕ Fin 2) (l : Fin r)
      (y : E3) (hy : y ∈ (tagSum a).cap) :
      width' l ≤ |⟪(u : E3), y⟫_ℝ - cut l| := by
    rcases a with a | i
    · rw [(hold a).2.2.2.2.2.2.1] at hy
      exact (hwidthold l).trans (S.caps_avoid a l y hy)
    · by_cases hl : l = k
      · subst l
        have hb := (tagSum (Sum.inr i)).cap_abs_height_bounds y hy
        rw [htagcut, (hnewphysical i).2.2.1,
          (E.newCap_spec i).2.2.2.1] at hb
        change 3 * c / 4 < |⟪(u : E3), y⟫_ℝ - cut k| ∧ _ at hb
        simp only [width', Function.update_self]
        linarith only [hb.1, hc]
      · have hb := (tagSum (Sum.inr i)).cap_outside_other_cut_buffer
          r cut D S.buffers_separated k (htagcut (Sum.inr i))
          (htagremoval (Sum.inr i)) l hl y hy
        exact (hwidthold l).trans ((S.width_le l).trans hb.le)
  let gamma : Fin (S.capCount + 2) ≃ (Fin S.capCount ⊕ Fin 2) :=
    finSumFinEquiv.symm
  let S' : FamilyCutState P u r cut D m0 B Phi (n + 1) psi' := {
    buffer_pos := S.buffer_pos
    buffers_separated := S.buffers_separated
    planar_disjoint := S.planar_disjoint
    family_smooth := S.family_smooth
    family_inverse := S.family_inverse
    embedding := hembed
    central_disjoint := hdisjoint
    width := width'
    width_pos := hwidthpos
    width_le := fun l => (hwidthold l).trans (S.width_le l)
    count := count'
    label := label'
    level_eq := hlevel'
    capCount := S.capCount + 2
    owner := fun a => ownerSum (gamma a)
    cap := fun a => tagSum (gamma a)
    birth := fun a => birthSum (gamma a)
    cap_profile := fun a => htagprofile (gamma a)
    cap_cut := fun a => htagcut (gamma a)
    cap_removal := fun a => htagremoval (gamma a)
    caps_disjoint := fun a b hab => hcapdisjoint (fun h => hab (gamma.injective h))
    caps_avoid := fun a => htagavoid (gamma a) }
  have hmeasure : S'.measure + 1 = S.measure := by
    change (∑ l : Fin r, count' l) + 1 = ∑ l : Fin r, S.count l
    rw [hcount, Finset.sum_update_of_mem (Finset.mem_univ k)]
    have hsum := Finset.sum_update_of_mem (Finset.mem_univ k) S.count (S.count k)
    rw [Function.update_eq_self] at hsum
    omega
  refine ⟨chosen, j, E, e, hcut, hprofile, hwidth, htube, hprotected,
    S', hcount, rfl, hmeasure, ?_, ?_, rfl, gamma, ?_, ?_, ?_, houter⟩
  · change range (label' k) = _
    exact (congrArg (fun v : Σ m : ℕ, Fin m ↪ Fin (m0 k) => range v.2)
      hpackk).trans hkeep
  · intro l hl
    change range (label' l) = _
    exact congrArg (fun v : Σ m : ℕ, Fin m ↪ Fin (m0 l) => range v.2)
      (hpackother l hl)
  · intro a
    have hf (b : Fin S.capCount ⊕ Fin 2) (hb : b = Sum.inl a) :
        birthSum b = S.birth a ∧
          (tagSum b).profile = (S.cap a).profile ∧
          (tagSum b).tube = (S.cap a).tube ∧
          (tagSum b).cutHeight = (S.cap a).cutHeight ∧
          (tagSum b).removal = (S.cap a).removal ∧
          (tagSum b).scale = (S.cap a).scale ∧
          (tagSum b).sign = (S.cap a).sign ∧
          (tagSum b).cap = (S.cap a).cap ∧
          (tagSum b).seam = (S.cap a).seam := by
      subst b
      exact ⟨rfl, hold a⟩
    exact hf _ (gamma.apply_symm_apply (Sum.inl a))
  · intro i
    have hf (b : Fin S.capCount ⊕ Fin 2) (hb : b = Sum.inr i) :
        ownerSum b = e.symm (Sum.inr i) ∧ birthSum b = k ∧ HEq (tagSum b) (E.newCap i) := by
      subst b
      exact ⟨(hnew i).1, rfl, (hnew i).2⟩
    exact hf _ (gamma.apply_symm_apply (Sum.inr i))
  · change (⋃ a : Fin (S.capCount + 2), (tagSum (gamma a)).cap) = _
    rw [← hcapunion]
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨gamma a, ha⟩
    · intro hy
      obtain ⟨a, ha⟩ := mem_iUnion.mp hy
      refine mem_iUnion.mpr ⟨gamma.symm a, ?_⟩
      exact (congrArg (fun b => (tagSum b).cap) (gamma.apply_symm_apply a)).symm ▸ ha

end PoincareConjecture.M25.Topology3D
