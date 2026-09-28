import PoincareConjecture.Proofs.M76.Brown.OrientedFlatteningCharts
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set SignType

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

variable {B X P ι : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace P]

private theorem exists_open_vertical_box {U : Set (B × ℝ)} (hU : IsOpen U)
    (p : B) (hp : (p, (0 : ℝ)) ∈ U) :
    ∃ W : Set B, IsOpen W ∧ p ∈ W ∧ ∃ r : ℝ, 0 < r ∧
      W ×ˢ Ioo (-r) r ⊆ U := by
  obtain ⟨W, V, hW, hpW, hV, hzero, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hU.mem_nhds hp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzero)
  refine ⟨W, hW, hpW, r, hr, ?_⟩
  intro z hz
  apply hsub ⟨hz.1, hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hz.2

private theorem exists_scalar_positive_sign {U : Set (B × ℝ)}
    (hU : IsOpen U) (g : B × ℝ → ℝ) (hg : ContinuousOn g U)
    (hzero : ∀ z ∈ U, g z = 0 ↔ z.2 = 0)
    (p : B) (hp : (p, (0 : ℝ)) ∈ U) :
    ∃ s : SignType, s ≠ 0 ∧ ∃ W : Set B, IsOpen W ∧ p ∈ W ∧
      ∃ r : ℝ, 0 < r ∧ W ×ˢ Ioo (-r) r ⊆ U ∧
        ∀ q ∈ W, ∀ t ∈ Ioo (0 : ℝ) r, sign (g (q, t)) = s := by
  obtain ⟨V, hV, hpV, r, hr, hsub⟩ := exists_open_vertical_box hU p hp
  have hhalf : r / 2 ∈ Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hgne (q : B) (hq : q ∈ V) : g (q, r / 2) ≠ 0 := by
    intro he
    have := (hzero _ (hsub ⟨hq, hhalf⟩)).mp he
    linarith
  let s := sign (g (p, r / 2))
  have hgc : ContinuousOn (fun q => sign (g (q, r / 2))) V := by
    have hc : ContinuousOn (fun q => g (q, r / 2)) V :=
      hg.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun q hq => hsub ⟨hq, hhalf⟩)
    intro q hq
    exact (continuousAt_sign_of_ne_zero (hgne q hq)).comp_continuousWithinAt
      (f := fun q => g (q, r / 2))
      (hc q hq)
  let W := V ∩ (fun q => sign (g (q, r / 2))) ⁻¹' {s}
  have hW : IsOpen W := hgc.isOpen_inter_preimage hV (isOpen_discrete _)
  refine ⟨s, sign_ne_zero.mpr (hgne p hpV), W, hW, ⟨hpV, rfl⟩,
    r, hr, fun z hz => hsub ⟨hz.1.1, hz.2⟩, ?_⟩
  intro q hq t ht
  have hside : ContinuousOn (fun t => sign (g (q, t))) (Ioo (0 : ℝ) r) := by
    have hc : ContinuousOn (fun t => g (q, t)) (Ioo (0 : ℝ) r) := by
      apply hg.comp (continuous_const.prodMk continuous_id).continuousOn
      intro t ht
      exact hsub ⟨hq.1, lt_trans (neg_lt_zero.mpr hr) ht.1, ht.2⟩
    intro t ht
    have htU : (q, t) ∈ U := hsub ⟨hq.1, by constructor <;> linarith [ht.1, ht.2]⟩
    apply (continuousAt_sign_of_ne_zero ?_).comp_continuousWithinAt
      (hc t ht)
    intro he
    exact (ne_of_gt ht.1) ((hzero _ htU).mp he)
  have hconn := (convex_Ioo (0 : ℝ) r).isPreconnected.image _ hside
  have heq := hconn.subsingleton (mem_image_of_mem _ ht)
    (mem_image_of_mem _ (show r / 2 ∈ Ioo (0 : ℝ) r from ⟨by linarith, by linarith⟩))
  exact heq.trans hq.2

def PositiveCollarSignAt (E : ι → OpenPartialHomeomorph X (P × ℝ))
    (F : B × ℝ → X) (p : B) (s : SignType) : Prop :=
  s ≠ 0 ∧ ∃ i : ι, ∃ W : Set B, IsOpen W ∧ p ∈ W ∧ ∃ r : ℝ, 0 < r ∧
    (∀ q ∈ W, F (q, 0) ∈ (E i).source) ∧
    ∀ q ∈ W, ∀ t ∈ Ioo (0 : ℝ) r, sign (E i (F (q, t))).2 = s

theorem exists_positiveCollarSignAt
    {S : Set X} {U : Set (B × ℝ)} (hU : IsOpen U)
    (F : B × ℝ → X) (hF : ContinuousOn F U)
    (hbase : ∀ p, (p, (0 : ℝ)) ∈ U)
    (hzero : ∀ z ∈ U, F z ∈ S ↔ z.2 = 0)
    (E : ι → OpenPartialHomeomorph X (P × ℝ))
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (p : B) : ∃ s, PositiveCollarSignAt E F p s := by
  obtain ⟨i, hpi⟩ := hcover (F (p, 0)) ((hzero _ (hbase p)).mpr rfl)
  let V := U ∩ F ⁻¹' (E i).source
  have hV : IsOpen V := hF.isOpen_inter_preimage hU (E i).open_source
  have hg : ContinuousOn (fun z => (E i (F z)).2) V :=
    ((E i).continuousOn.comp (hF.mono inter_subset_left) (fun _ hz => hz.2)).snd
  obtain ⟨s, hs, W, hW, hpW, r, hr, hsub, hsign⟩ :=
    exists_scalar_positive_sign hV _ hg
      (fun z hz => (hpair i (F z) hz.2).symm.trans (hzero z hz.1)) p ⟨hbase p, hpi⟩
  refine ⟨s, hs, i, W, hW, hpW, r, hr, ?_, hsign⟩
  intro q hq
  exact (hsub ⟨hq, neg_lt_zero.mpr hr, hr⟩).2

theorem PositiveCollarSignAt.exists_open
    {E : ι → OpenPartialHomeomorph X (P × ℝ)} {F : B × ℝ → X}
    {p : B} {s : SignType} (hs : PositiveCollarSignAt E F p s) :
    ∃ W : Set B, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, PositiveCollarSignAt E F q s := by
  obtain ⟨hs, i, W, hW, hpW, r, hr, hbase, hsign⟩ := hs
  exact ⟨W, hW, hpW, fun q hq => ⟨hs, i, W, hW, hq, r, hr, hbase, hsign⟩⟩

theorem PositiveCollarSignAt.unique
    {S : Set X} {E : ι → OpenPartialHomeomorph X (P × ℝ)} {F : B × ℝ → X}
    (hcompat : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V)
    {p : B} (hF : ContinuousAt F (p, (0 : ℝ))) (hbase : F (p, 0) ∈ S)
    {s t : SignType} (hs : PositiveCollarSignAt E F p s)
    (ht : PositiveCollarSignAt E F p t) : s = t := by
  obtain ⟨_, i, W, _, hpW, r, hr, hi, hs⟩ := hs
  obtain ⟨_, j, W', _, hpW', r', hr', hj, ht⟩ := ht
  obtain ⟨V, hV, hpV, heq⟩ := hcompat i j ⟨F (p, 0), hbase⟩ ⟨hi p hpW, hj p hpW'⟩
  have hfc : ContinuousAt (fun u : ℝ => F (p, u)) 0 :=
    hF.comp (continuous_const.prodMk continuous_id).continuousAt
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp
    (hfc.preimage_mem_nhds (hV.mem_nhds hpV))
  let a := min r (min r' d) / 2
  have ha : 0 < a := by dsimp [a]; exact half_pos (lt_min hr (lt_min hr' hd))
  have hal : a < min r (min r' d) := by
    dsimp [a]
    exact half_lt_self (lt_min hr (lt_min hr' hd))
  have har : a < r := hal.trans_le (min_le_left _ _)
  have har' : a < r' := hal.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have had : a < d := hal.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpoint : F (p, a) ∈ V := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha] using had)
  exact (hs p hpW a ⟨ha, har⟩).symm.trans
    ((heq hpoint).trans (ht p hpW' a ⟨ha, har'⟩))

theorem PositiveCollarSignAt.in_chart
    {S : Set X} {U : Set (B × ℝ)} (hU : IsOpen U)
    {E : ι → OpenPartialHomeomorph X (P × ℝ)} {F : B × ℝ → X}
    (hF : ContinuousOn F U)
    (hcompat : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V)
    {p : B} (hp : (p, (0 : ℝ)) ∈ U) (hbase : F (p, 0) ∈ S)
    {s : SignType} (hs : PositiveCollarSignAt E F p s)
    (i : ι) (hi : F (p, 0) ∈ (E i).source) :
    ∃ W : Set B, IsOpen W ∧ p ∈ W ∧ ∃ r : ℝ, 0 < r ∧
      (∀ q ∈ W, F (q, 0) ∈ (E i).source) ∧
      ∀ q ∈ W, ∀ t ∈ Ioo (0 : ℝ) r, sign (E i (F (q, t))).2 = s := by
  obtain ⟨_, j, W, hW, hpW, r, hr, hj, hsign⟩ := hs
  obtain ⟨V, hV, hpV, heq⟩ := hcompat j i ⟨F (p, 0), hbase⟩ ⟨hj p hpW, hi⟩
  have hD : IsOpen (U ∩ F ⁻¹' (V ∩ (E i).source)) :=
    hF.isOpen_inter_preimage hU (hV.inter (E i).open_source)
  obtain ⟨W', hW', hpW', r', hr', hsub⟩ :=
    exists_open_vertical_box hD p ⟨hp, hpV, hi⟩
  refine ⟨W ∩ W', hW.inter hW', ⟨hpW, hpW'⟩,
    min r r', lt_min hr hr', ?_, ?_⟩
  · intro q hq
    exact (hsub ⟨hq.2, neg_lt_zero.mpr hr', hr'⟩).2.2
  · intro q hq t ht
    have htr : t < r := ht.2.trans_le (min_le_left _ _)
    have htr' : t < r' := ht.2.trans_le (min_le_right _ _)
    have htV : F (q, t) ∈ V :=
      (hsub ⟨hq.2, lt_trans (neg_lt_zero.mpr hr') ht.1, htr'⟩).2.1
    exact (heq htV).symm.trans (hsign q hq.1 t ⟨ht.1, htr⟩)

theorem exists_collar_positive_normal_label
    {S : Set X} {U : Set (B × ℝ)} (hU : IsOpen U)
    (F : B × ℝ → X) (hF : ContinuousOn F U)
    (hbase : ∀ p, (p, (0 : ℝ)) ∈ U)
    (hzero : ∀ z ∈ U, F z ∈ S ↔ z.2 = 0)
    (E : ι → OpenPartialHomeomorph X (P × ℝ))
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0))
    (hcompat : ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => sign (E i y).2) (fun y => sign (E j y).2) V) :
    ∃ ν : B → SignType, IsLocallyConstant ν ∧ (∀ p, ν p ≠ 0) ∧
      ∀ p, PositiveCollarSignAt E F p (ν p) := by
  classical
  choose ν hν using exists_positiveCollarSignAt hU F hF hbase hzero E hcover hpair
  refine ⟨ν, ?_, fun p => (hν p).1, hν⟩
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨W, hW, hpW, hWν⟩ := (hν p).exists_open
  refine ⟨W, hW, hpW, ?_⟩
  intro q hq
  exact (hν q).unique hcompat (hF.continuousAt (hU.mem_nhds (hbase q)))
    ((hzero _ (hbase q)).mpr rfl) (hWν q hq)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
