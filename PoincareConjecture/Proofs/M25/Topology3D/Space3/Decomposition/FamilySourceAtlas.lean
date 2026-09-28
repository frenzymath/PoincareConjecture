import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutState
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


def FamilyCutState.sourceCore
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (i : Fin n) : Set UnitTwoSphere :=
  (univ : Set UnitTwoSphere) \
    ⋃ a : {a : Fin S.capCount // S.owner a = i},
      (S.cap a.1).sourceCapInterior


theorem FamilyCutState.sourceCore_mem_and_seams
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi) :
    (∀ (i : Fin n) (q : UnitTwoSphere),
      q ∈ S.sourceCore i ↔
        ∀ a : Fin S.capCount,
          psi i (q, 0) ∉ (S.cap a).cap \ (S.cap a).seam) ∧
      ∀ a : Fin S.capCount,
        (S.cap a).sourceCap ∩ S.sourceCore (S.owner a) =
          (S.cap a).sourceSeam := by
  classical
  have hinj (i : Fin n) : Function.Injective (fun q : UnitTwoSphere => psi i (q, 0)) := by
    intro q q' hq
    exact congrArg Prod.fst ((S.embedding i).2.1 (by simp) (by simp) hq)
  have hnative (a : Fin S.capCount) (q : UnitTwoSphere) :
      q ∈ (S.cap a).sourceCapInterior ↔
        q ∈ (S.cap a).sourceCap \ (S.cap a).sourceSeam := by
    rw [← (S.cap a).sourceCap_diff_interior]
    have hsub := (S.cap a).sourceCapInterior_subset
    constructor
    · intro hq
      exact ⟨hsub hq, fun h => h.2 hq⟩
    · rintro ⟨hcap, hnot⟩
      by_contra hq
      exact hnot ⟨hcap, hq⟩
  have hphysical (a : Fin S.capCount) (q : UnitTwoSphere) :
      q ∈ (S.cap a).sourceCapInterior ↔
        psi (S.owner a) (q, 0) ∈ (S.cap a).cap \ (S.cap a).seam := by
    rw [hnative a q]
    constructor
    · rintro ⟨hcap, hseam⟩
      refine ⟨⟨q, hcap, rfl⟩, ?_⟩
      rintro ⟨q', hq', heq⟩
      exact hseam ((hinj (S.owner a) heq) ▸ hq')
    · rintro ⟨⟨q', hq', heq⟩, hseam⟩
      refine ⟨(hinj (S.owner a) heq) ▸ hq', ?_⟩
      intro hq
      exact hseam ⟨q, hq, rfl⟩
  have hmem (i : Fin n) (q : UnitTwoSphere) :
      q ∈ S.sourceCore i ↔
        ∀ a : Fin S.capCount, psi i (q, 0) ∉ (S.cap a).cap \ (S.cap a).seam := by
    constructor
    · intro hq a ha
      have howner : S.owner a = i := by
        by_contra hne
        rcases ha.1 with ⟨p, _hp, heq⟩
        exact disjoint_left.mp (S.central_disjoint hne) ⟨p, heq⟩ ⟨q, rfl⟩
      have hi : q ∈ (S.cap a).sourceCapInterior :=
        (hphysical a q).mpr (by simpa only [howner] using ha)
      exact hq.2 (mem_iUnion.mpr ⟨⟨a, howner⟩, hi⟩)
    · intro hq
      refine ⟨mem_univ _, ?_⟩
      intro hi
      obtain ⟨a, ha⟩ := mem_iUnion.mp hi
      exact hq a.1 (by simpa only [a.2] using (hphysical a.1 q).mp ha)
  refine ⟨hmem, ?_⟩
  intro a
  ext q
  constructor
  · rintro ⟨hcap, hcore⟩
    rw [← (S.cap a).sourceCap_diff_interior]
    exact ⟨hcap, fun hi => (hmem (S.owner a) q).mp hcore a ((hphysical a q).mp hi)⟩
  · intro hseam
    have hcap := (show q ∈ (S.cap a).sourceCap \ (S.cap a).sourceCapInterior by
      rw [(S.cap a).sourceCap_diff_interior]
      exact hseam).1
    refine ⟨hcap, (hmem (S.owner a) q).mpr ?_⟩
    intro b hb
    by_cases hba : b = a
    · subst b
      exact hb.2 ⟨q, hseam, rfl⟩
    · exact disjoint_left.mp (S.caps_disjoint hba) hb.1 ⟨q, hcap, rfl⟩


structure FamilySourceAtlas
    (original : UnitTwoSphere × ℝ → E3)
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi) where
  chart : Fin n → OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere
  chart_smooth : ∀ i : Fin n,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i) (chart i).source
  chart_inverse : ∀ i : Fin n,
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i).symm (chart i).target
  core_subset_source : ∀ i : Fin n, S.sourceCore i ⊆ (chart i).source
  timeScale : Fin n → ℝ
  timeScale_ne_zero : ∀ i : Fin n, timeScale i ≠ 0
  timeScale_abs_le : ∀ i : Fin n, |timeScale i| ≤ 1
  collar_eq : ∀ i : Fin n, ∀ q ∈ (chart i).source,
    ∀ s : ℝ, |s| < 1 →
      psi i (q, s) = original (chart i q, timeScale i * s)


theorem RegularSurgeryEvent.newCap_native_source
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) :
    ∀ i : Fin 2,
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
        (E.newCap i).sourceChart q = q) ∧
      (E.newCap i).sourceCapInterior =
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 < 0} ∧
      (E.newCap i).sourceCap =
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      (E.newCap i).sourceSeam =
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
  intro i
  let c := E.data.width / 2 * (1 - E.radius)
  let sigma : ℝ := ![1, -1] i
  let e := ![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i
  have hsigma : |sigma| = 1 := by fin_cases i <;> norm_num [sigma]
  obtain ⟨_hd, hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  have hjoin : sigma * c ∈ Ioo (-E.data.width) E.data.width := by
    apply abs_lt.mp
    rw [abs_mul, hsigma, one_mul, abs_of_pos hc]
    exact hck.trans hkw
  have hequator (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
      parent (surgeryNorthChart E.matching e q, 0) =
        E.profile.capMap E.data.tube E.cutHeight sigma c E.scale q := by
    change parent (surgeryNorthChart E.matching e q, 0) =
      surgeryCapMap E.profile.horizontal E.profile.vertical
        E.profile.horizontal_smooth E.profile.vertical_smooth
        (fun z => (E.profile.horizontal_pos z).ne')
        (fun x => (E.profile.vertical_pos x).ne') E.data.tube E.cutHeight sigma c E.scale q
    rw [surgeryNorthChart_equator_formula E.matching e E.data.sourceCollar
      sigma (E.data.width / 2) E.radius_mem.1 E.radius_mem.2 E.radius_near
      E.matching_circle (E.radial i) q hq, E.data.reconstruction _ _ hjoin,
      surgeryCapMap, surgeryCapCoordinates_cylinder E.profile.horizontal E.profile.vertical
        E.profile.horizontal_smooth E.profile.vertical_smooth
        (fun z => (E.profile.horizontal_pos z).ne')
        (fun x => (E.profile.vertical_pos x).ne')
        E.profile.horizontal_near E.profile.vertical_far E.cutHeight sigma c E.scale q
        (by rw [hq]; norm_num)]
    simp only [hq, mul_zero, add_zero]
  have hchild (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      E.child i (q, 0) = E.profile.capMap E.data.tube E.cutHeight sigma c E.scale q := by
    rw [E.child_central]
    change levelPaste (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2)
      (fun q => parent (surgeryNorthChart E.matching e q, 0))
      (E.profile.capMap E.data.tube E.cutHeight sigma c E.scale) q = _
    rcases lt_or_eq_of_le hq with hneg | heq
    · exact levelPaste_of_neg _ _ _ hneg
    · rw [levelPaste_of_nonneg (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2)
        _ _ heq.ge]
      exact hequator q heq
  have hidentity (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      (E.newCap i).sourceChart q = q := by
    have htag := (E.newCap i).central_eq q (hq.trans_lt (E.newCap i).overlap_pos)
    obtain ⟨hp, ht, hcut, hrem, hl, hs⟩ := E.newCap_spec i
    rw [hp, ht, hcut, hrem, hl, hs] at htag
    exact congrArg Prod.fst ((E.child_embedding i).2.1 (by simp) (by simp)
      (htag.trans (hchild q hq).symm))
  refine ⟨hidentity, ?_, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hidentity p hp.le]
      exact hp
    · intro hq
      exact ⟨q, hq, hidentity q hq.le⟩
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hidentity p hp]
      exact hp
    · intro hq
      exact ⟨q, hq, hidentity q hq⟩
  · ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hidentity p hp.le]
      exact hp
    · intro hq
      exact ⟨q, hq, hidentity q hq.le⟩


theorem FamilySourceAtlas.exists_initial
    (original : UnitTwoSphere × ℝ → E3)
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    (S : FamilyCutState P u r cut D m0 B Phi 1
      (fun _ : Fin 1 => original))
    (hcap : S.capCount = 0) :
    ∃ A : FamilySourceAtlas original S,
      (∀ i : Fin 1, S.sourceCore i = univ) ∧
      ∀ i : Fin 1,
        A.chart i = OpenPartialHomeomorph.refl UnitTwoSphere ∧
        A.timeScale i = 1 := by
  let A : FamilySourceAtlas original S := {
    chart := fun _ => OpenPartialHomeomorph.refl UnitTwoSphere
    chart_smooth := fun _ => contMDiffOn_id
    chart_inverse := fun _ => contMDiffOn_id
    core_subset_source := fun _ => subset_univ _
    timeScale := fun _ => 1
    timeScale_ne_zero := fun _ => one_ne_zero
    timeScale_abs_le := fun _ => by norm_num
    collar_eq := fun _ _ _ _ _ => by simp }
  refine ⟨A, ?_, fun _ => ⟨rfl, rfl⟩⟩
  intro i
  ext q
  simp only [FamilyCutState.sourceCore, mem_sdiff, mem_univ, true_and, mem_iUnion,
    not_exists, iff_true]
  intro a
  exact False.elim (Nat.not_lt_zero _ (a.1.isLt.trans_le hcap.le))


theorem FamilySourceAtlas.exists_surgery_step
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (A : FamilySourceAtlas original S)
    (j : Fin n) (E : RegularSurgeryEvent (psi j) u)
    (e : Fin (n + 1) ≃ ({i : Fin n // i ≠ j} ⊕ Fin 2))
    (S' : FamilyCutState P u r cut D m0 B Phi (n + 1)
      (fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1)
        E.child (e a)))
    (gamma : Fin S'.capCount ≃ (Fin S.capCount ⊕ Fin 2))
    (hold : ∀ a : Fin S.capCount,
      let b := gamma.symm (Sum.inl a)
      (S'.cap b).cap = (S.cap a).cap ∧
        (S'.cap b).seam = (S.cap a).seam)
    (hnew : ∀ i : Fin 2,
      let b := gamma.symm (Sum.inr i)
      S'.owner b = e.symm (Sum.inr i) ∧
        HEq (S'.cap b) (E.newCap i)) :
    ∃ A' : FamilySourceAtlas original S',
      (∀ h : {i : Fin n // i ≠ j},
        A'.chart (e.symm (Sum.inl h)) = A.chart h.1 ∧
        A'.timeScale (e.symm (Sum.inl h)) = A.timeScale h.1 ∧
        S'.sourceCore (e.symm (Sum.inl h)) = S.sourceCore h.1) ∧
      ∀ i : Fin 2,
        A'.chart (e.symm (Sum.inr i)) =
          (E.retainedChart i).trans (A.chart j) ∧
        A'.timeScale (e.symm (Sum.inr i)) =
          A.timeScale j * E.retainedTime i ∧
        S'.sourceCore (e.symm (Sum.inr i)) =
          {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ∩
            (E.retainedChart i) ⁻¹' S.sourceCore j ∧
        S'.sourceCore (e.symm (Sum.inr i)) ⊆
          (E.retainedChart i).source ∧
        (E.retainedChart i) '' S'.sourceCore (e.symm (Sum.inr i)) =
          S.sourceCore j ∩
            ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
              closedBall (0 : E2) E.radius) := by
  classical
  let psi' : Fin (n + 1) → UnitTwoSphere × ℝ → E3 :=
    fun a => Sum.elim (fun i : {i : Fin n // i ≠ j} => psi i.1) E.child (e a)
  let old : {i : Fin n // i ≠ j} → Fin (n + 1) := fun h => e.symm (Sum.inl h)
  let child : Fin 2 → Fin (n + 1) := fun i => e.symm (Sum.inr i)
  let newTag : Fin 2 → Fin S'.capCount := fun i => gamma.symm (Sum.inr i)
  have holdmap (h : {i : Fin n // i ≠ j}) : psi' (old h) = psi h.1 := by
    simp only [psi', old, Equiv.apply_symm_apply, Sum.elim_inl]
  have hchildmap (i : Fin 2) : psi' (child i) = E.child i := by
    simp only [psi', child, Equiv.apply_symm_apply, Sum.elim_inr]
  have hnewowner (i : Fin 2) : S'.owner (newTag i) = child i := (hnew i).1
  have hsourceEq {f g : UnitTwoSphere × ℝ → E3} (hfg : f = g)
      {C : SurgeryCapTag f u} {N : SurgeryCapTag g u} (hCN : HEq C N) :
      C.sourceCapInterior = N.sourceCapInterior := by
    subst g
    cases eq_of_heq hCN
    rfl
  have hnewsource (i : Fin 2) : (S'.cap (newTag i)).sourceCapInterior =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 < 0} := by
    have hfg : psi' (S'.owner (newTag i)) = E.child i := by
      rw [hnewowner, hchildmap]
    exact (hsourceEq hfg (hnew i).2).trans (E.newCap_native_source i).2.1
  have hinj (a : Fin (n + 1)) :
      Function.Injective (fun q : UnitTwoSphere => psi' a (q, 0)) := by
    intro q q' heq
    exact congrArg Prod.fst ((S'.embedding a).2.1 (by simp) (by simp) heq)
  have hinterior (a : Fin S'.capCount) (q : UnitTwoSphere) :
      psi' (S'.owner a) (q, 0) ∈ (S'.cap a).cap \ (S'.cap a).seam ↔
        q ∈ (S'.cap a).sourceCapInterior := by
    constructor
    · rintro ⟨⟨p, hp, heq⟩, hseam⟩
      have hcap : q ∈ (S'.cap a).sourceCap := (hinj (S'.owner a) heq) ▸ hp
      by_contra hnot
      apply hseam
      refine ⟨q, ?_, rfl⟩
      rw [← (S'.cap a).sourceCap_diff_interior]
      exact ⟨hcap, hnot⟩
    · intro hq
      refine ⟨⟨q, (S'.cap a).sourceCapInterior_subset hq, rfl⟩, ?_⟩
      rintro ⟨p, hp, heq⟩
      have hs : q ∈ (S'.cap a).sourceSeam := (hinj (S'.owner a) heq) ▸ hp
      rw [← (S'.cap a).sourceCap_diff_interior] at hs
      exact hs.2 hq
  have hnewinterior (i : Fin 2) (q : UnitTwoSphere) :
      psi' (child i) (q, 0) ∈ (S'.cap (newTag i)).cap \ (S'.cap (newTag i)).seam ↔
        (heightCoordinates (q : E3)).2 < 0 := by
    rw [← hnewowner i, hinterior, hnewsource]
    rfl
  have hforeign (a : Fin (n + 1)) (b : Fin S'.capCount) (hba : S'.owner b ≠ a)
      (q : UnitTwoSphere) : psi' a (q, 0) ∉ (S'.cap b).cap := by
    rintro ⟨p, _hp, heq⟩
    exact disjoint_left.mp (S'.central_disjoint hba) ⟨p, heq⟩ ⟨q, rfl⟩
  have hchildold (i : Fin 2) (h : {i : Fin n // i ≠ j}) : child i ≠ old h := by
    intro heq
    have he := e.symm.injective heq
    cases he
  have hchildinj : Function.Injective child := by
    intro i l hil
    exact Sum.inr.inj (e.symm.injective hil)
  have hmem := S.sourceCore_mem_and_seams.1
  have hmem' := S'.sourceCore_mem_and_seams.1
  have holdcore (h : {i : Fin n // i ≠ j}) : S'.sourceCore (old h) = S.sourceCore h.1 := by
    ext q
    rw [hmem', hmem]
    constructor
    · intro hq a
      have havoid := hq (gamma.symm (Sum.inl a))
      change psi' (old h) (q, 0) ∉ _ at havoid
      rw [holdmap, (hold a).1, (hold a).2] at havoid
      exact havoid
    · intro hq a
      rcases ha : gamma a with b | i
      · have hea : a = gamma.symm (Sum.inl b) := (gamma.eq_symm_apply).mpr ha
        subst a
        change psi' (old h) (q, 0) ∉ _
        rw [holdmap, (hold b).1, (hold b).2]
        exact hq b
      · have hea : a = newTag i := (gamma.eq_symm_apply).mpr ha
        subst a
        intro hbad
        exact hforeign (old h) (newTag i)
          (by rw [hnewowner]; exact hchildold i h) q hbad.1
  have hnorth (i : Fin 2) :
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆
        (E.retainedChart i).source := (E.retained_spec i).2.2.2.2.2.2.1
  have hcentral (i : Fin 2) (q : UnitTwoSphere)
      (hq : q ∈ (E.retainedChart i).source) :
      psi' (child i) (q, 0) = psi j (E.retainedChart i q, 0) := by
    rw [hchildmap]
    simpa only [mul_zero] using
      (E.retained_spec i).2.2.2.2.2.2.2.2.2.2 q hq 0 (by norm_num)
  have hchildcore (i : Fin 2) : S'.sourceCore (child i) =
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ∩
        (E.retainedChart i) ⁻¹' S.sourceCore j := by
    ext q
    constructor
    · intro hq
      have hnonneg : 0 ≤ (heightCoordinates (q : E3)).2 := by
        apply le_of_not_gt
        intro hneg
        exact (hmem' (child i) q).mp hq (newTag i) ((hnewinterior i q).mpr hneg)
      refine ⟨hnonneg, (hmem j (E.retainedChart i q)).mpr ?_⟩
      intro a ha
      have havoid := (hmem' (child i) q).mp hq (gamma.symm (Sum.inl a))
      change psi' (child i) (q, 0) ∉ _ at havoid
      rw [hcentral i q (hnorth i hnonneg), (hold a).1, (hold a).2] at havoid
      exact havoid ha
    · rintro ⟨hq, hcore⟩
      apply (hmem' (child i) q).mpr
      intro a
      rcases ha : gamma a with b | l
      · have hea : a = gamma.symm (Sum.inl b) := (gamma.eq_symm_apply).mpr ha
        subst a
        change psi' (child i) (q, 0) ∉ _
        rw [hcentral i q (hnorth i hq), (hold b).1, (hold b).2]
        exact (hmem j (E.retainedChart i q)).mp hcore b
      · have hea : a = newTag l := (gamma.eq_symm_apply).mpr ha
        subst a
        by_cases hli : l = i
        · subst l
          intro hbad
          exact (not_lt_of_ge hq) ((hnewinterior i q).mp hbad)
        · intro hbad
          exact hforeign (child i) (newTag l)
            (by rw [hnewowner]; exact fun heq => hli (hchildinj heq)) q hbad.1
  have hcoresource (i : Fin 2) :
      S'.sourceCore (child i) ⊆ (E.retainedChart i).source := by
    intro q hq
    rw [hchildcore] at hq
    exact hnorth i hq.1
  have hcoreimage (i : Fin 2) : (E.retainedChart i) '' S'.sourceCore (child i) =
      S.sourceCore j ∩
        ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
          closedBall (0 : E2) E.radius) := by
    have hret : (E.retainedChart i : UnitTwoSphere → UnitTwoSphere) =
        surgeryNorthChart E.matching
          (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) :=
      funext (E.retained_spec i).2.2.2.2.1
    have himage : (E.retainedChart i) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
        (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
          closedBall (0 : E2) E.radius := by
      rw [hret]
      exact surgeryNorthChart_image_hemisphere _ _ E.matching_closedBall
    rw [hchildcore]
    ext q
    constructor
    · rintro ⟨p, ⟨hp, hcore⟩, rfl⟩
      exact ⟨hcore, himage ▸ mem_image_of_mem _ hp⟩
    · rintro ⟨hcore, him⟩
      rw [← himage] at him
      obtain ⟨p, hp, rfl⟩ := him
      exact ⟨p, ⟨hp, hcore⟩, rfl⟩
  let chart' : Fin (n + 1) → OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere :=
    fun a => Sum.elim (fun h : {i : Fin n // i ≠ j} => A.chart h.1)
      (fun i : Fin 2 => (E.retainedChart i).trans (A.chart j)) (e a)
  let scale' : Fin (n + 1) → ℝ := fun a =>
    Sum.elim (fun h : {i : Fin n // i ≠ j} => A.timeScale h.1)
      (fun i : Fin 2 => A.timeScale j * E.retainedTime i) (e a)
  have hchartold (h : {i : Fin n // i ≠ j}) : chart' (old h) = A.chart h.1 := by
    simp only [chart', old, Equiv.apply_symm_apply, Sum.elim_inl]
  have hchartchild (i : Fin 2) :
      chart' (child i) = (E.retainedChart i).trans (A.chart j) := by
    simp only [chart', child, Equiv.apply_symm_apply, Sum.elim_inr]
  have hscaleold (h : {i : Fin n // i ≠ j}) : scale' (old h) = A.timeScale h.1 := by
    simp only [scale', old, Equiv.apply_symm_apply, Sum.elim_inl]
  have hscalechild (i : Fin 2) : scale' (child i) = A.timeScale j * E.retainedTime i := by
    simp only [scale', child, Equiv.apply_symm_apply, Sum.elim_inr]
  let A' : FamilySourceAtlas original S' := {
    chart := chart'
    chart_smooth := by
      intro a
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartold]
        exact A.chart_smooth h.1
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartchild, OpenPartialHomeomorph.trans_source]
        exact (A.chart_smooth j).comp' (E.retained_spec i).2.2.2.2.2.2.2.2.1
    chart_inverse := by
      intro a
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartold]
        exact A.chart_inverse h.1
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartchild, OpenPartialHomeomorph.trans_target]
        exact (E.retained_spec i).2.2.2.2.2.2.2.2.2.1.comp' (A.chart_inverse j)
    core_subset_source := by
      intro a
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartold, holdcore]
        exact A.core_subset_source h.1
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        rw [hchartchild, OpenPartialHomeomorph.trans_source, hchildcore]
        exact fun _ hq => ⟨hnorth i hq.1, A.core_subset_source j hq.2⟩
    timeScale := scale'
    timeScale_ne_zero := by
      intro a
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        rw [hscaleold]
        exact A.timeScale_ne_zero h.1
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        rw [hscalechild]
        exact mul_ne_zero (A.timeScale_ne_zero j) (E.retained_spec i).1
    timeScale_abs_le := by
      intro a
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        rw [hscaleold]
        exact A.timeScale_abs_le h.1
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        rw [hscalechild, abs_mul]
        exact (mul_le_mul (A.timeScale_abs_le j) (E.retained_spec i).2.1.le
          (abs_nonneg _) zero_le_one).trans_eq (mul_one _)
    collar_eq := by
      intro a q hq s hs
      rcases ha : e a with h | i
      · have hea : a = old h := (e.eq_symm_apply).mpr ha
        subst a
        change psi h.1 (q, s) = original (chart' (old h) q, scale' (old h) * s)
        rw [hchartold, hscaleold]
        rw [hchartold] at hq
        exact A.collar_eq h.1 q hq s hs
      · have hea : a = child i := (e.eq_symm_apply).mpr ha
        subst a
        change E.child i (q, s) = original (chart' (child i) q, scale' (child i) * s)
        rw [hchartchild, hscalechild]
        rw [hchartchild, OpenPartialHomeomorph.trans_source] at hq
        have htime : |E.retainedTime i * s| < 1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (E.retained_spec i).2.1.le
            (abs_nonneg s)).trans_lt (by simpa only [one_mul] using hs)
        rw [(E.retained_spec i).2.2.2.2.2.2.2.2.2.2 q hq.1 s hs,
          A.collar_eq j (E.retainedChart i q) hq.2 (E.retainedTime i * s) htime]
        rw [mul_assoc]
        rfl }
  refine ⟨A', ?_, ?_⟩
  · intro h
    exact ⟨hchartold h, hscaleold h, holdcore h⟩
  · intro i
    exact ⟨hchartchild i, hscalechild i, hchildcore i, hcoresource i, hcoreimage i⟩

end PoincareConjecture.M25.Topology3D
