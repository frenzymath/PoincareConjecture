import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularGluing
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Real
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

private def annularProfile (R d : ℝ) (z : LoopPlane) : ℝ :=
  smoothTransition ((‖z‖ - (R - d)) / (2 * d))

private theorem annularProfile_continuous (R d : ℝ) : Continuous (annularProfile R d) :=
  (smoothTransition.contDiff (n := 0)).continuous.comp
    ((continuous_norm.sub continuous_const).div_const _)

private theorem annularProfile_mem (R d : ℝ) (z : LoopPlane) :
    annularProfile R d z ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

private theorem annularProfile_one {R d : ℝ} (hd : 0 < d)
    {z : LoopPlane} (hz : R + d ≤ ‖z‖) : annularProfile R d z = 1 :=
  smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
    (by linarith only [hz]))

private theorem annularProfile_zero {R d : ℝ} (hd : 0 < d)
    {z : LoopPlane} (hz : ‖z‖ ≤ R - d) : annularProfile R d z = 0 :=
  smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hz) (by positivity))

variable {M : Type*} [TopologicalSpace M]

private def annularStart (C : ℝ × (M × M) → M) (f v : LoopPlane → M)
    (R d : ℝ) (x : unitInterval × LoopPlane) : M :=
  if R + d ≤ ‖x.2‖ then f x.2
    else C (1 - x.1.val * (1 - annularProfile R d x.2), f x.2, v x.2)

private theorem annularStart_time_mem (t : unitInterval) (R d : ℝ) (z : LoopPlane) :
    1 - t.val * (1 - annularProfile R d z) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨ht0, ht1⟩ := t.property
  obtain ⟨hp0, hp1⟩ := annularProfile_mem R d z
  constructor
  · nlinarith [mul_nonneg ht0 hp0]
  · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hp1)]

private theorem annularStart_continuous
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ U, ContinuousAt C (t, v))
    {f v : LoopPlane → M} (hf : Continuous f) (hv : Continuous v)
    {R d : ℝ} (hd : 0 < d)
    (hpairs : ∀ z : LoopPlane, ‖z‖ < R + 2 * d → (f z, v z) ∈ U) :
    Continuous (annularStart C f v R d) := by
  have htime : Continuous (fun x : unitInterval × LoopPlane =>
      1 - x.1.val * (1 - annularProfile R d x.2)) :=
    continuous_const.sub ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub ((annularProfile_continuous R d).comp continuous_snd)))
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hout : R + d < ‖x.2‖
  · apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds hout] with y hy
    exact (if_pos hy.le).symm
  have hx : ‖x.2‖ < R + 2 * d := by linarith only [le_of_not_gt hout, hd]
  have hin : ContinuousAt (fun y : unitInterval × LoopPlane =>
      (1 - y.1.val * (1 - annularProfile R d y.2), f y.2, v y.2)) x :=
    htime.continuousAt.prodMk
      ((hf.comp continuous_snd).continuousAt.prodMk (hv.comp continuous_snd).continuousAt)
  have hc : ContinuousAt (fun y : unitInterval × LoopPlane =>
      C (1 - y.1.val * (1 - annularProfile R d y.2), f y.2, v y.2)) x :=
    (hC _ (annularStart_time_mem x.1 R d x.2) _ (hpairs x.2 hx)).comp
      (f := fun y : unitInterval × LoopPlane =>
        (1 - y.1.val * (1 - annularProfile R d y.2), f y.2, v y.2)) hin
  apply hc.congr
  filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hx] with y hy
  dsimp only [annularStart]
  split_ifs with ho
  · rw [annularProfile_one hd ho, sub_self, mul_zero, sub_zero, h1 _ (hpairs y.2 hy)]
  · rfl

omit [TopologicalSpace M] in
private theorem annularStart_zero
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (f v : LoopPlane → M) {R d : ℝ} (hd : 0 < d)
    (hpairs : ∀ z : LoopPlane, ‖z‖ < R + 2 * d → (f z, v z) ∈ U)
    (z : LoopPlane) : annularStart C f v R d (0, z) = f z := by
  dsimp only [annularStart]
  split_ifs with ho
  · rfl
  · simp only [Set.Icc.coe_zero, zero_mul, sub_zero]
    exact h1 _ (hpairs z (by linarith only [lt_of_not_ge ho, hd]))

omit [TopologicalSpace M] in
private theorem annularStart_one
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (f v : LoopPlane → M) {R d : ℝ} (hd : 0 < d) (z : LoopPlane) :
    annularStart C f v R d (1, z) = suAnnularBlend C f v R d z := by
  dsimp only [annularStart, suAnnularBlend]
  split_ifs with ho hi
  · rfl
  · simp only [Set.Icc.coe_one, one_mul, sub_sub_cancel]
    rw [annularProfile_zero hd hi, h0]
  · simp only [Set.Icc.coe_one, one_mul, sub_sub_cancel]
    rfl

theorem suAnnularBlend_continuous_family
    {X : Type*} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h0 : ∀ p q, C (0, p, q) = q) (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ U, ContinuousAt C (t, v))
    {f a : X × LoopPlane → M} (hf : Continuous f) (ha : Continuous a)
    {R d : ℝ} (hd : 0 < d)
    (hpairs : ∀ x : X × LoopPlane, R - 2 * d < ‖x.2‖ →
      ‖x.2‖ < R + 2 * d → (f x, a x) ∈ U) :
    Continuous (fun x : X × LoopPlane =>
      suAnnularBlend C (fun z => f (x.1, z)) (fun z => a (x.1, z)) R d x.2) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hout : R + d < ‖x.2‖
  · apply hf.continuousAt.congr
    filter_upwards [(isOpen_lt continuous_const continuous_snd.norm).mem_nhds hout] with y hy
    exact (suAnnularBlend_outer C (fun z => f (y.1, z))
      (fun z => a (y.1, z)) hy.le).symm
  by_cases hin : ‖x.2‖ < R - d
  · apply ha.continuousAt.congr
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds hin] with y hy
    exact (suAnnularBlend_inner C (fun z => f (y.1, z))
      (fun z => a (y.1, z)) hd hy.le).symm
  have hlo : R - d ≤ ‖x.2‖ := le_of_not_gt hin
  have hhi : ‖x.2‖ ≤ R + d := le_of_not_gt hout
  have hx := hpairs x (by linarith only [hlo, hd]) (by linarith only [hhi, hd])
  have hinput : ContinuousAt
      (fun y : X × LoopPlane => (annularProfile R d y.2, f y, a y)) x :=
    ((annularProfile_continuous R d).comp continuous_snd).continuousAt.prodMk
      (hf.continuousAt.prodMk ha.continuousAt)
  have hcont : ContinuousAt
    (fun y : X × LoopPlane => C (annularProfile R d y.2, f y, a y)) x :=
    (hC _ (annularProfile_mem R d x.2) _ hx).comp
      (f := fun y : X × LoopPlane => (annularProfile R d y.2, f y, a y)) hinput
  apply hcont.congr
  have hlo' : R - 2 * d < ‖x.2‖ := by linarith only [hlo, hd]
  have hhi' : ‖x.2‖ < R + 2 * d := by linarith only [hhi, hd]
  have hnear : ∀ᶠ y in 𝓝 x, R - 2 * d < ‖y.2‖ ∧ ‖y.2‖ < R + 2 * d :=
    ((isOpen_lt continuous_const continuous_snd.norm).inter
      (isOpen_lt continuous_snd.norm continuous_const)).mem_nhds ⟨hlo', hhi'⟩
  filter_upwards [hnear] with y hy
  have hpair := hpairs y hy.1 hy.2
  change C (annularProfile R d y.2, f y, a y) = _
  by_cases ho : R + d ≤ ‖y.2‖
  · rw [suAnnularBlend_outer C _ _ ho, annularProfile_one hd ho, h1 _ hpair]
  by_cases hi : ‖y.2‖ ≤ R - d
  · rw [suAnnularBlend_inner C _ _ hd hi, annularProfile_zero hd hi, h0]
  · simp only [suAnnularBlend, if_neg ho, if_neg hi]
    rfl

set_option maxHeartbeats 400000 in

theorem suAnnularBlend_plane_homotopy
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h0 : ∀ p q, C (0, p, q) = q) (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ U, ContinuousAt C (t, v))
    (f v a : C(LoopPlane, M)) (H : v.Homotopy a) {R d : ℝ} (hd : 0 < d)
    (hfirst : ∀ z : LoopPlane, ‖z‖ < R + 2 * d → (f z, v z) ∈ U)
    (hfamily : ∀ x : unitInterval × LoopPlane, R - 2 * d < ‖x.2‖ →
      ‖x.2‖ < R + 2 * d → (f x.2, H x) ∈ U) :
    ∃ (B : C(LoopPlane, M)) (G : f.Homotopy B),
      (∀ z, B z = suAnnularBlend C f a R d z) ∧
      ∀ t : unitInterval, ∀ z : LoopPlane, R + d ≤ ‖z‖ → G (t, z) = f z := by
  have hc₀ := annularStart_continuous C h1 hC f.continuous v.continuous hd hfirst
  let B₀ : C(LoopPlane, M) := ⟨fun z => annularStart C f v R d (1, z),
    hc₀.comp (continuous_const.prodMk continuous_id)⟩
  let G₀ : f.Homotopy B₀ := {
    toFun := annularStart C f v R d
    continuous_toFun := hc₀
    map_zero_left := annularStart_zero C h1 f v hd hfirst
    map_one_left := fun _ => rfl
  }
  have hc₁ : Continuous (fun x : unitInterval × LoopPlane =>
      suAnnularBlend C f (fun z => H (x.1, z)) R d x.2) :=
    suAnnularBlend_continuous_family C h0 h1 hC
      (f.continuous.comp continuous_snd) H.continuous hd hfamily
  let B : C(LoopPlane, M) := ⟨fun z =>
    suAnnularBlend C f (fun y => H (1, y)) R d z,
    hc₁.comp (f := fun z : LoopPlane => ((1 : unitInterval), z))
      (continuous_const.prodMk continuous_id)⟩
  let G₁ : B₀.Homotopy B := {
    toFun := fun x => suAnnularBlend C f (fun z => H (x.1, z)) R d x.2
    continuous_toFun := hc₁
    map_zero_left := fun z => by
      change suAnnularBlend C f (fun y => H (0, y)) R d z = annularStart C f v R d (1, z)
      simp only [H.apply_zero]
      exact (annularStart_one C h0 f v hd z).symm
    map_one_left := fun _ => rfl
  }
  refine ⟨B, G₀.trans G₁, ?_, ?_⟩
  · intro z
    change suAnnularBlend C f (fun y => H (1, y)) R d z = _
    simp only [H.apply_one]
  · intro t z hz
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact if_pos hz
    · dsimp only [G₁, DFunLike.coe, ContinuousMap.Homotopy.instFunLike]
      exact suAnnularBlend_outer C f _ hz

theorem suSpherePlanePatch_continuous_family
    {X : Type*} [TopologicalSpace X]
    {f : UnitTwoSphere → M} (hf : Continuous f) (c : UnitTwoSphere)
    {F : X × LoopPlane → M} (hF : Continuous F) {R : ℝ}
    (hout : ∀ x : X, ∀ z : LoopPlane, R < ‖z‖ → F (x, z) = f ((chartAt LoopPlane c).symm z)) :
    Continuous (fun x : X × UnitTwoSphere => suSpherePlanePatch f c (fun z => F (x.1, z)) x.2) := by
  classical
  let e := chartAt LoopPlane c
  let K := e.symm '' closedBall (0 : LoopPlane) R
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) R).image
    (suSphereChart_smooth c).continuous
  have hKsource : K ⊆ e.source := by
    rintro _ ⟨z, _, rfl⟩
    apply e.map_target
    rw [suSphereChart_target]
    trivial
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x.2 ∈ e.source
  · have he : ContinuousAt e x.2 := e.continuousOn.continuousAt (e.open_source.mem_nhds hx)
    apply (hF.continuousAt.comp (continuous_fst.continuousAt.prodMk
      (he.comp continuous_snd.continuousAt))).congr
    filter_upwards [(e.open_source.preimage continuous_snd).mem_nhds hx] with y hy
    exact (if_pos hy).symm
  · have hxK : x.2 ∉ K := fun h => hx (hKsource h)
    apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [(hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hxK] with y hy
    exact (suSpherePlanePatch_outside f c (hout y.1) hy).symm

theorem suSpherePlanePatch_homotopic
    (f : C(UnitTwoSphere, M)) (c : UnitTwoSphere)
    (F : C(unitInterval × LoopPlane, M)) {R : ℝ}
    (hout : ∀ t : unitInterval, ∀ z : LoopPlane, R < ‖z‖ →
      F (t, z) = f ((chartAt LoopPlane c).symm z))
    (hzero : ∀ z : LoopPlane, F (0, z) = f ((chartAt LoopPlane c).symm z)) :
    ∃ h : C(UnitTwoSphere, M), h.Homotopic f ∧
      ∀ p, h p = suSpherePlanePatch f c (fun z => F (1, z)) p := by
  classical
  have hc := suSpherePlanePatch_continuous_family f.continuous c F.continuous hout
  let h : C(UnitTwoSphere, M) := ⟨fun p => suSpherePlanePatch f c (fun z => F (1, z)) p,
    hc.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨h, ?_, fun _ => rfl⟩
  apply ContinuousMap.Homotopic.symm
  refine ⟨{
    toFun := fun x => suSpherePlanePatch f c (fun z => F (x.1, z)) x.2
    continuous_toFun := hc
    map_zero_left := ?_
    map_one_left := fun _ => rfl
  }⟩
  intro p
  dsimp only [suSpherePlanePatch]
  split_ifs with hp
  · rw [hzero, (chartAt LoopPlane c).left_inv hp]
  · rfl

end PoincareConjecture.M60
