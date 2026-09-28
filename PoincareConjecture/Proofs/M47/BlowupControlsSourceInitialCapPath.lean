import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapTangent
import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem source_initial_cap_contact_path
    {F : SurgeryFlowData.{u}} (standard : RepairedStandardCapExistenceData F.standard_initial)
    {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {A eta : ℝ} (hA : 2 * (F.standard_initial.cylindrical_end.radius + 5) < A)
    {J : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F standard.flow A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
      HEq (e.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    (s : ℝ) (hs : s ∈ J) {y : (F.slice t).carrier}
    (hy : y ∈ ((F.event t hT).caps i).carrier) :
    ∃ gamma : ℝ → (F.slice (t + s / ((F.parameters.h t)⁻¹ ^ 2))).carrier,
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1) ∧
      gamma 0 = e.forward s hs y ∧
      gamma 1 = e.forward s hs ((F.event t hT).caps i).tip ∧
      MapsTo gamma (Icc (0 : ℝ) 1)
        (e.forward s hs '' (F.metric t).ball ((F.event t hT).caps i).tip
          (A * F.parameters.h t)) ∧
      (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).pathELength gamma 0 1 <
        ENNReal.ofReal (4 * (F.standard_initial.cylindrical_end.radius + 5) *
          F.parameters.h t) := by
  let A0 := F.standard_initial.cylindrical_end.radius
  let D0 := 2 * (A0 + 5)
  let h := F.parameters.h t
  have hA0 : 0 < A0 := F.standard_initial.cylindrical_end.radius_pos
  have hD0 : 0 < D0 := by dsimp only [D0]; positivity
  have hApos : 0 < A := hD0.trans hA
  have hA5 : A0 + 5 < A := by linarith only [hA, hA0]
  have hyU := inserted_cap_subset_persistence_ball hT i hA5 hy
  obtain ⟨z, hz, hzy⟩ := comparison.choose_spec.2.2.2.1.symm ▸ hyU
  have hdist := Proofs.M47.cap_birth_tip_distance_near_one hApos e initial comparison
    hzero hbase hh heta hetaSmall hz
  have houter := ((F.event t hT).caps i).outer_ball hy
  have houterReal : ((F.metric t).edist ((F.event t hT).caps i).tip y).toReal ≤
      (A0 + 5) * h := by
    have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top houter
    change ((F.metric t).edist ((F.event t hT).caps i).tip y).toReal ≤
      (ENNReal.ofReal (h * (A0 + 5))).toReal at hbound
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ h * (A0 + 5))] at hbound
    nlinarith only [hbound]
  have hdistSmall : (F.standard_initial.metric.edist 0 z).toReal < D0 := by
    rw [hzy] at hdist
    calc
      _ ≤ (101 / 100 : ℝ) * h⁻¹ * ((F.metric t).edist
          ((F.event t hT).caps i).tip y).toReal := hdist
      _ ≤ (101 / 100 : ℝ) * h⁻¹ * ((A0 + 5) * h) :=
        mul_le_mul_of_nonneg_left houterReal (by positivity)
      _ = (101 / 100 : ℝ) * (A0 + 5) := by
        field_simp [show h ≠ 0 from hh.ne']
      _ < D0 := by dsimp only [D0]; linarith only [hA0]
  have hzD0 : z ∈ F.standard_initial.metric.ball 0 D0 := by
    change F.standard_initial.metric.edist 0 z < ENNReal.ofReal D0
    apply (ENNReal.toReal_lt_toReal (F.standard_initial.metric.edist_ne_top 0 z)
      ENNReal.ofReal_ne_top).mp
    rwa [ENNReal.toReal_ofReal hD0.le]
  obtain ⟨p, hp0, hp1, hp, hlength, hball⟩ :=
    F.standard_initial.metric.exists_short_path_in_ball 0 z hzD0
  let clock : ℝ → ℝ := fun r => 1 - r
  let path := p ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.sub contDiff_id
  have hclockmap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 1) := by
    intro r hr
    constructor <;> dsimp only [clock] <;> linarith only [hr.1, hr.2]
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc 0 1) :=
    hp.comp hclock.contMDiff.contMDiffOn hclockmap
  have hpathball : MapsTo path (Icc (0 : ℝ) 1) (F.standard_initial.metric.ball 0 A) := by
    intro r hr
    exact (hball (hclockmap hr)).trans_le (ENNReal.ofReal_le_ofReal hA.le)
  have hreverse : F.standard_initial.metric.pathELength path 0 1 =
      F.standard_initial.metric.pathELength p 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨F.standard_initial.metric.toRiemannianMetric⟩
    have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) p (Icc (clock 1) (clock 0)) := by
      simpa only [clock, sub_self, sub_zero] using hp.mdifferentiableOn one_ne_zero
    have heq := Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 3) zero_le_one
      (show AntitoneOn clock (Icc (0 : ℝ) 1) from
        fun _ _ _ _ hab => sub_le_sub_left hab 1)
      (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! heq using 1
    simp only [clock, sub_self, sub_zero]
    rfl
  let f := actualCapSliceChart e initial comparison s hs
  have hf (w : StandardCapSpace) (hw : w ∈ F.standard_initial.metric.ball 0 A) :
      ContMDiffAt (𝓡 3) (𝓡 3) 1 f w := by
    have hwf : w ∈ f.source := by rwa [actualCapSliceChart_source]
    exact (f.contMDiffOn_toFun.contMDiffAt (f.open_source.mem_nhds hwf)).of_le (by simp)
  have hfull : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ path) (Icc 0 1) :=
    (show ContMDiffOn (𝓡 3) (𝓡 3) 1 f (F.standard_initial.metric.ball 0 A) from
      fun w hw => (hf w hw).contMDiffWithinAt).comp hpath hpathball
  refine ⟨f ∘ path, hfull, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, path, clock, sub_zero, hp1,
      actualCapSliceChart_apply, hzy, f]
  · simp only [Function.comp_apply, path, clock, sub_self, hp0,
      actualCapSliceChart_apply, initial.tip_eq, f]
  · intro r hr
    refine ⟨initial.chart (path r), ?_, rfl⟩
    exact comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart (hpathball hr)
  · have hnorm (w : StandardCapSpace) (hw : w ∈ F.standard_initial.metric.ball 0 A)
        (v : TangentSpace (𝓡 3) w) :=
      source_initial_cap_chart_tangent_le standard e initial comparison hh heta hetaSmall
        s hs hw v
    have hlen := F.standard_initial.metric.pathELength_comp_le_of_pointwise_tangentNorm_le
      (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))) f hf
      (by positivity : 0 ≤ 2 * h) hnorm path 0 1 hpath hpathball
    rw [hreverse] at hlen
    have hstrict := ENNReal.mul_lt_mul_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (show 0 < 2 * h by positivity)))
      ENNReal.ofReal_ne_top hlength
    apply hlen.trans_lt (hstrict.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * h)]
    congr 1
    dsimp only [D0, A0, h]
    ring

end PoincareConjecture.M47
