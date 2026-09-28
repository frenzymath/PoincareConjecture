import PoincareConjecture.Proofs.M64.Mathlib.ClosedFirstExit
import PoincareConjecture.Proofs.M64.Mathlib.CompactRadialTube
import PoincareConjecture.Proofs.M64.Mathlib.LocalLiftNormControl
import PoincareConjecture.Proofs.M64.Mathlib.RadialCornerGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64_exists_earlier_radial_digon_contact
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] (F : OpenPartialHomeomorph E X)
    {v theta : E} {R s : ℝ} (hs : 0 < s) (hR : ‖v‖ ≤ R)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ F.source)
    {beta : ℝ → X} (hb : ContinuousOn beta (Icc 0 s)) (hi : InjOn beta (Icc 0 s))
    (hbase : beta 0 = F 0) (hend : beta s = F v)
    {U : Set X}
    (hfront : frontier U = (fun t : ℝ => F (t • v)) '' Icc 0 1 ∪ beta '' Icc 0 s)
    {phi : E → ℝ × ℝ} {J : E →L[ℝ] ℝ × ℝ}
    (hphi : HasFDerivAt phi J 0) (hzero : phi 0 = 0)
    (hcorner : ∀ᶠ z in 𝓝 (0 : E),
      0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2 → F z ∈ closure U)
    (hv1 : 0 < (J v).1) (hv2 : (J v).2 = 0)
    (ht1 : (J theta).1 = 0) (ht2 : 0 < (J theta).2)
    (hescape : ∀ᶠ a in 𝓝[>] (1 : ℝ), F (a • v) ∉ closure U)
    (hshort : ∀ᶠ b in 𝓝[<] s, ‖F.symm (beta b)‖ < ‖v‖) :
    ∃ b ∈ Ioo 0 s, ∃ z ∈ F.source,
      ‖z‖ ≤ R ∧ (∀ t ∈ Icc (0 : ℝ) 1, t • z ∈ F.source ∧ F (t • z) ∈ closure U) ∧
        F z = beta b ∧ z ≠ b • theta := by
  have hvne : v ≠ 0 := by
    intro hv
    simp only [hv, map_zero, Prod.fst_zero, lt_self_iff_false] at hv1
  have hvs : v ∈ F.source := by simpa only [one_smul] using hsegment 1 ⟨zero_le_one, le_rfl⟩
  have hlocal := m64_eventually_lift_contact_norm_le F hvs hs.le hb hi hend.symm hshort
  obtain ⟨O, hO, hOS, hsegO, hnorm⟩ :=
    m64_exists_radial_contact_neighborhood F.open_source hvne hR hsegment hlocal
  obtain ⟨A0, hA0, C, hC, htube⟩ := m64_exists_extended_radial_tube hO hsegO
  have hvC : v ∈ C := mem_of_mem_nhds hC
  have hsmall : ∀ᶠ a in 𝓝[>] (1 : ℝ), a ∈ Ioo 1 A0 := Ioo_mem_nhdsGT hA0
  obtain ⟨A, hAI, hAvout⟩ := (hsmall.and hescape).exists
  have hA : 0 < A := zero_lt_one.trans hAI.1
  have hAvs : A • v ∈ F.source := hOS (htube v hvC A ⟨hA.le, hAI.2.le⟩)
  have hcont : ContinuousAt (fun w : E => F (A • w)) v :=
    ((F.continuousOn (A • v) hAvs).continuousAt (F.open_source.mem_nhds hAvs)).comp
      (continuous_const.smul continuous_id).continuousAt
  have hC' : ∀ᶠ w in 𝓝 v, w ∈ C := hC
  have hnear : ∀ᶠ w in 𝓝 v, w ∈ C ∧ F (A • w) ∉ closure U :=
    hC'.and (hcont.eventually (isClosed_closure.isOpen_compl.mem_nhds hAvout))
  have hpert : Tendsto (fun eps : ℝ => v + eps • theta) (𝓝 0) (𝓝 v) := by
    have hc : Continuous (fun eps : ℝ => v + eps • theta) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hnear' : ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      v + eps • theta ∈ C ∧ F (A • (v + eps • theta)) ∉ closure U :=
    (hpert.eventually hnear).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  obtain ⟨eps, heps, hwC, hwout⟩ := (hpos.and hnear').exists
  have hepspos : 0 < eps := heps
  let w := v + eps • theta
  have hw1 : (J w).1 = (J v).1 := by simp [w, ht1]
  have hw2 : (J w).2 = eps * (J theta).2 := by simp [w, hv2]
  have hwpos : 0 < (J w).1 ∧ 0 < (J w).2 := by
    rw [hw1, hw2]
    exact ⟨hv1, mul_pos hepspos ht2⟩
  have hwO (t : ℝ) (ht : t ∈ Icc 0 A) : t • w ∈ O :=
    htube w hwC t ⟨ht.1, ht.2.trans hAI.2.le⟩
  have hpath : ContinuousOn (fun t : ℝ => F (t • w)) (Icc 0 A) :=
    F.continuousOn.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => hOS (hwO t ht))
  have hstart : F ((0 : ℝ) • w) ∈ closure U := by
    apply frontier_subset_closure
    rw [hfront]
    exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  obtain ⟨a, ha, hafront, hconf⟩ := m64_exists_first_exit_closed hA hpath isClosed_closure
    hstart (m64_radial_enters_positive_corner hphi hzero hcorner hwpos) hwout
  have has : a • w ∈ F.source := hOS (hwO a ⟨ha.1.le, ha.2.le⟩)
  have havoid (t : ℝ) (ht : t ∈ Icc 0 1) : F (a • w) ≠ F (t • v) := by
    intro heq
    have hvect := F.injOn has (hsegment t ht) heq
    have hcoord := congrArg (fun z : E => (J z).2) hvect
    have hpos : 0 < a * (J w).2 := mul_pos ha.1 hwpos.2
    simp only [map_smul, Prod.smul_snd, smul_eq_mul, hv2, mul_zero] at hcoord
    exact hpos.ne' hcoord
  have hcontact : F (a • w) ∈ frontier U := frontier_closure_subset hafront
  rw [hfront] at hcontact
  rcases hcontact with ⟨t, ht, heq⟩ | ⟨b, hbI, heq⟩
  · exact False.elim (havoid t ht heq.symm)
  have hb0 : 0 < b := lt_of_le_of_ne hbI.1 (by
    intro heq0
    have h := heq0 ▸ heq
    rw [hbase] at h
    exact havoid 0 ⟨le_rfl, zero_le_one⟩ (by simpa only [zero_smul] using h.symm))
  have hbs : b < s := lt_of_le_of_ne hbI.2 (by
    intro heqs
    have h := heqs ▸ heq
    rw [hend] at h
    exact havoid 1 ⟨zero_le_one, le_rfl⟩ (by simpa only [one_smul] using h.symm))
  refine ⟨b, ⟨hb0, hbs⟩, a • w, has,
    hnorm (a • w) (hwO a ⟨ha.1.le, ha.2.le⟩) b hbI heq.symm, ?_, heq.symm, ?_⟩
  · intro t ht
    have hta : t * a ∈ Icc 0 a :=
      ⟨mul_nonneg ht.1 ha.1.le, by nlinarith only [ht.2, ha.1]⟩
    rw [smul_smul]
    exact ⟨hOS (hwO (t * a) ⟨hta.1, hta.2.trans ha.2.le⟩), hconf hta⟩
  · intro heqv
    have hcoord := congrArg (fun z : E => (J z).1) heqv
    have hpos : 0 < a * (J w).1 := mul_pos ha.1 hwpos.1
    simp only [map_smul, Prod.smul_fst, smul_eq_mul, ht1, mul_zero] at hcoord
    exact hpos.ne' hcoord

end PoincareConjecture
