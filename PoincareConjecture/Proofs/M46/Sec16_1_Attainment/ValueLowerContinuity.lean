import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.CappedSliceValue
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.JointSublevel
import Mathlib.Topology.Semicontinuity.Basic










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}



theorem cappedSliceAction_sublevel_compact
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {a c d : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ T - start) (hd : d < C.barrier) :
    IsCompact {b : ℝ | b ∈ Icc a c ∧ cappedSliceAction G T x C.barrier b ≤ d} := by
  classical
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : T2Space (G.Horizontal x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3)) G.Horizontal x
  let : T2Space (G.Horizontal x × ℝ) := inferInstance
  have hbound (b : ℝ) (hb : b ∈ Icc a c) : b ^ 2 ≤ T - start := by
    have hbpos := ha.trans_le hb.1
    have hbc := (sq_le_sq₀ hbpos.le (hbpos.le.trans hb.2)).mpr hb.2
    exact hbc.trans hc
  let D := max 0 d
  have hDB : D < C.barrier := max_lt
    (lt_of_le_of_lt (by positivity) C.barrier_large) hd
  let B : Set (G.Horizontal x × ℝ) :=
    {z | z.2 ∈ Icc a c ∧ z ∈ E.domain ∧ E.action z.1 z.2 ≤ D}
  have hB : IsCompact B := exponential_joint_action_sublevel_compact hM04 hM12 LG E ha
    (le_max_left _ _)
    (fun b hb => hstrip ⟨by linarith [hbound b hb], sub_le_self _ (sq_nonneg b)⟩)
    C.cage_compact (fun Z b hb hZ hZD =>
      actionConfinement_exponential_mem C E (ha.trans_le hb.1) (hbound b hb) hZ
        (hZD.trans_lt hDB))
  have hcont : ContinuousOn (fun z : G.Horizontal x × ℝ => E.action z.1 z.2) B :=
    (LG.exponential.action_differential T x E).1.continuousOn.mono
      (fun _ hz => ⟨hz.2.1, ha.trans_le hz.1.1⟩)
  let A := B ∩ (fun z : G.Horizontal x × ℝ => E.action z.1 z.2) ⁻¹' Iic d
  have hA : IsCompact A := hB.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed hB.isClosed isClosed_Iic) inter_subset_left
  have heq : {b : ℝ | b ∈ Icc a c ∧ cappedSliceAction G T x C.barrier b ≤ d} =
      Prod.snd '' A := by
    ext b
    constructor
    · rintro ⟨hb, hval⟩
      obtain ⟨Z, hZ, _, hact⟩ := cappedSliceAction_exponential hM04 hM12 LG E C
        (ha.trans_le hb.1) (hbound b hb) (hval.trans_lt hd)
      exact ⟨(Z, b), ⟨⟨hb, hZ, hact.le.trans (hval.trans (le_max_right _ _))⟩,
        hact.le.trans hval⟩, rfl⟩
    · rintro ⟨⟨Z, s⟩, hs, rfl⟩
      have hm := (cappedSliceAction_alternative hM04 hM12 LG E C
        (ha.trans_le hs.1.1.1) (hbound s hs.1.1)).2.1
        (E.gamma Z s) (E.path Z s hs.1.2.1 (ha.trans_le hs.1.1.1))
      rw [← E.action_eq Z s hs.1.2.1 (ha.trans_le hs.1.1.1)] at hm
      exact ⟨hs.1.1, hm.trans hs.2⟩
  rw [heq]
  exact hA.image continuous_snd



theorem cappedSliceAction_lowerSemicontinuousOn
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {a c : ℝ} (ha : 0 < a) (hc : c ^ 2 ≤ T - start) :
    LowerSemicontinuousOn (cappedSliceAction G T x C.barrier) (Icc a c) := by
  intro b hb d hd
  have hbpos := ha.trans_le hb.1
  have hbound : b ^ 2 ≤ T - start :=
    ((sq_le_sq₀ hbpos.le (hbpos.le.trans hb.2)).mpr hb.2).trans hc
  have hdB := hd.trans_le
    (cappedSliceAction_alternative hM04 hM12 LG E C hbpos hbound).1
  have hclosed := (cappedSliceAction_sublevel_compact hM04 hM12 LG E C hstrip ha hc hdB).isClosed
  have hnot : b ∈ {s : ℝ | s ∈ Icc a c ∧ cappedSliceAction G T x C.barrier s ≤ d}ᶜ :=
    fun h => (not_le_of_gt hd) h.2
  have hnear := mem_nhdsWithin_of_mem_nhds (t := Icc a c)
    (hclosed.isOpen_compl.mem_nhds hnot)
  filter_upwards [hnear, self_mem_nhdsWithin] with s hs hsI
  exact lt_of_not_ge (fun hsd => hs ⟨hsI, hsd⟩)

end PoincareConjecture.Proofs.M46
