import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.SliceValues
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.JointSublevel










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}




theorem confinementRegion_compact_minima
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G) (E : M14ExponentialFamily G T x)
    (C : ActionConfinement G T start x) (hstrip : Icc start T ⊆ I.domain)
    (hcontinuous : ∀ a c : ℝ, 0 < a → c ^ 2 ≤ T - start →
      ContinuousOn (cappedSliceAction G T x C.barrier) (Icc a c))
    (hbound : ∀ b : ℝ, 0 < b → b ^ 2 ≤ T - start →
      cappedSliceAction G T x C.barrier b ≤ 3 * b)
    (a b : ℝ) (habStrip : Icc a b ⊆ Ico start T) :
    IsCompact {y : G.Point | y ∈ confinementRegion C ∧
      G.spacetime.timeFunction y ∈ Icc a b ∧
      ∀ z ∈ confinementRegion C, G.spacetime.timeFunction z = G.spacetime.timeFunction y →
        M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x y ≤
          M14ActionValue G T 0 (T - G.spacetime.timeFunction y) x z} := by
  by_cases hab : a ≤ b
  swap
  · have he : Icc a b = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp only [he, mem_empty_iff_false, false_and, and_false, ofPred_false, isCompact_empty]
  have haStrip := habStrip ⟨le_rfl, hab⟩
  have hbStrip := habStrip ⟨hab, le_rfl⟩
  let aS := Real.sqrt (T - b)
  let cS := Real.sqrt (T - a)
  have haS : 0 < aS := Real.sqrt_pos.mpr (sub_pos.mpr hbStrip.2)
  have haSsq : aS ^ 2 = T - b := Real.sq_sqrt (sub_nonneg.mpr hbStrip.2.le)
  have hcSsq : cS ^ 2 = T - a := Real.sq_sqrt (sub_nonneg.mpr haStrip.2.le)
  have hcSStart : cS ^ 2 ≤ T - start := by rw [hcSsq]; exact sub_le_sub_left haStrip.1 T
  have hsRange (s : ℝ) (hs : s ∈ Icc aS cS) :
      0 < s ∧ s ^ 2 ≤ T - start ∧ T - s ^ 2 ∈ Icc a b := by
    have hspos := haS.trans_le hs.1
    have hlow := (sq_le_sq₀ haS.le hspos.le).mpr hs.1
    have hhigh := (sq_le_sq₀ hspos.le (Real.sqrt_nonneg (T - a))).mpr hs.2
    rw [haSsq] at hlow
    rw [hcSsq] at hhigh
    exact ⟨hspos, hhigh.trans (sub_le_sub_left haStrip.1 T), by constructor <;> linarith⟩
  let D := 3 * Real.sqrt (T - start)
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hDB : D < C.barrier := C.barrier_large
  have hvalue (s : ℝ) (hs : s ∈ Icc aS cS) :
      cappedSliceAction G T x C.barrier s ≤ D := by
    have hsdata := hsRange s hs
    apply (hbound s hsdata.1 hsdata.2.1).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    exact (Real.le_sqrt hsdata.1.le ((sq_nonneg s).trans hsdata.2.1)).mpr hsdata.2.1
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let J : Set (G.Horizontal x × ℝ) :=
    {z | z.2 ∈ Icc aS cS ∧ z ∈ E.domain ∧ E.action z.1 z.2 ≤ D}
  have hJ : IsCompact J := exponential_joint_action_sublevel_compact hM04 hM12 LG E haS hD
    (fun s hs => hstrip (Ico_subset_Icc_self (habStrip (hsRange s hs).2.2)))
    C.cage_compact (fun Z s hs hZ haction =>
      actionConfinement_exponential_mem C E (hsRange s hs).1 (hsRange s hs).2.1 hZ
        (haction.trans_lt hDB))
  have hE : ContinuousOn (fun z : G.Horizontal x × ℝ => E.action z.1 z.2) J :=
    (LG.exponential.action_differential T x E).1.continuousOn.mono
      (fun z hz => ⟨hz.2.1, haS.trans_le hz.1.1⟩)
  have hm : ContinuousOn (fun z : G.Horizontal x × ℝ => cappedSliceAction G T x C.barrier z.2) J :=
    (hcontinuous aS cS haS hcSStart).comp continuousOn_snd (fun _ hz => hz.1)
  let K : Set (G.Horizontal x × ℝ) :=
    {z ∈ J | E.action z.1 z.2 = cappedSliceAction G T x C.barrier z.2}
  have hK : IsCompact K := hJ.of_isClosed_subset (hJ.isClosed.isClosed_eq hE hm) (fun _ hz => hz.1)
  have himage : IsCompact ((fun z : G.Horizontal x × ℝ => E.gamma z.1 z.2) '' K) :=
    hK.image_of_continuousOn (E.joint_continuous.mono (fun _ hz => hz.1.2.1))
  convert himage using 1
  ext y
  constructor
  · rintro ⟨hy, hyt, hminimum⟩
    let s := Real.sqrt (T - G.spacetime.timeFunction y)
    have hs : s ∈ Icc aS cS :=
      ⟨Real.sqrt_le_sqrt (sub_le_sub_left hyt.2 T), Real.sqrt_le_sqrt (sub_le_sub_left hyt.1 T)⟩
    have hsdata := hsRange s hs
    have htime : T - G.spacetime.timeFunction y = s ^ 2 :=
      (Real.sq_sqrt (sub_nonneg.mpr (habStrip hyt).2.le)).symm
    have hyt' : G.spacetime.timeFunction y = T - s ^ 2 := by rw [← htime]; ring
    have heq := (confinementRegion_minimum_iff hM04 hM12 LG E C hsdata.1 hsdata.2.1
      ((hvalue s hs).trans_lt hDB) hy hyt').mp hminimum
    obtain ⟨p0, hp0⟩ : ∃ p0 : M14BackwardPath G T 0 (s ^ 2) x y,
        M14BackwardLAction G p0 < C.barrier := by
      have hr := hy.2
      rw [htime] at hr
      exact hr
    obtain ⟨p, hp⟩ := actionConfinement_attained hM12 C (sq_pos_of_pos hsdata.1) hsdata.2.1 p0 hp0
    obtain ⟨Z, hZsqrt, htrace, hend⟩ := minimizing_exponential_branch LG E p hp
    have hZ : (Z, s) ∈ E.domain := by simpa only [Real.sqrt_sq hsdata.1.le] using hZsqrt
    have haction : E.action Z s = cappedSliceAction G T x C.barrier s :=
      (represented_minimizer_action E hsdata.1 p hZ htrace).1.trans
        ((M14.action_eq_actionValue_of_minimizing p hp).trans heq)
    refine ⟨(Z, s), ⟨⟨hs, hZ, haction.le.trans (hvalue s hs)⟩, haction⟩, ?_⟩
    simpa only [Real.sqrt_sq hsdata.1.le] using hend
  · rintro ⟨z, hz, rfl⟩
    have hsdata := hsRange z.2 hz.1.1
    have hclock := E.clock z.1 z.2 hz.1.2.1
    have htime : T - G.spacetime.timeFunction (E.gamma z.1 z.2) = z.2 ^ 2 := by rw [hclock]; ring
    let p := E.path z.1 z.2 hz.1.2.1 hsdata.1
    have haction : M14BackwardLAction G p = cappedSliceAction G T x C.barrier z.2 :=
      (E.action_eq z.1 z.2 hz.1.2.1 hsdata.1).symm.trans hz.2
    have hp : M14IsMinimizing p := fun q => haction.le.trans
      ((cappedSliceAction_alternative hM04 hM12 LG E C hsdata.1 hsdata.2.1).2.1 _ q)
    have hy : E.gamma z.1 z.2 ∈ confinementRegion C := by
      refine ⟨by rw [hclock]; exact habStrip hsdata.2.2, ?_⟩
      rw [htime]
      exact ⟨p, haction.le.trans_lt ((hvalue z.2 hz.1.1).trans_lt hDB)⟩
    refine ⟨hy, by rw [hclock]; exact hsdata.2.2, ?_⟩
    apply (confinementRegion_minimum_iff hM04 hM12 LG E C hsdata.1 hsdata.2.1
      ((hvalue z.2 hz.1.1).trans_lt hDB) hy hclock).mpr
    exact (M14.action_eq_actionValue_of_minimizing p hp).symm.trans haction

end PoincareConjecture.Proofs.M46
