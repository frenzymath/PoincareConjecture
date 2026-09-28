import PoincareConjecture.Proofs.M76.Brown.NormalSignGerms
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Basic









set_option autoImplicit false

open Set Metric SignType

namespace BrownCollar

private theorem normal_sign_eq_of_preconnected {X : Type*} [TopologicalSpace X]
    {T : Set X} (hT : IsPreconnected T) (g : X → ℝ)
    (hg : ContinuousOn g T) (hne : ∀ z ∈ T, g z ≠ 0)
    {x y : X} (hx : x ∈ T) (hy : y ∈ T) : sign (g x) = sign (g y) := by
  have hc : ContinuousOn (fun z => sign (g z)) T := fun z hz =>
    (continuousAt_sign_of_ne_zero (hne z hz)).comp_continuousWithinAt (hg z hz)
  exact (hT.image _ hc).subsingleton (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)

variable {P Q : Type*} [TopologicalSpace P] [LocallyConnectedSpace P]
  [TopologicalSpace Q]




theorem exists_normalSignAt_of_locallyConnected
    (e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ))
    (hpair : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0)
    (p : P) (hp : (p, (0 : ℝ)) ∈ e.source) :
    ∃ s : SignType, NormalSignAt e p s := by
  obtain ⟨O, V, hO, hpO, hV, h0V, hOV⟩ :=
    mem_nhds_prod_iff'.mp (e.open_source.mem_nhds hp)
  obtain ⟨W, hWO, hW, hpW, hWc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace P) p O (hO.mem_nhds hpO)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let U := W ×ˢ Ioo (-r) r
  let Up := W ×ˢ Ioo (0 : ℝ) r
  let Um := W ×ˢ Ioo (-r) (0 : ℝ)
  have hU : IsOpen U := hW.prod isOpen_Ioo
  have hpU : (p, (0 : ℝ)) ∈ U := ⟨hpW, neg_lt_zero.mpr hr, hr⟩
  have hUs : U ⊆ e.source := by
    intro z hz
    apply hOV
    refine ⟨hWO hz.1, hball ?_⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hz.2
  have hUp : Up ⊆ U := fun z hz =>
    ⟨hz.1, lt_trans (neg_lt_zero.mpr hr) hz.2.1, hz.2.2⟩
  have hUm : Um ⊆ U := fun z hz => ⟨hz.1, hz.2.1, lt_trans hz.2.2 hr⟩
  have hUpc : IsPreconnected Up :=
    hWc.isPreconnected.prod (convex_Ioo (0 : ℝ) r).isPreconnected
  have hUmc : IsPreconnected Um :=
    hWc.isPreconnected.prod (convex_Ioo (-r) (0 : ℝ)).isPreconnected
  have hUpne : ∀ z ∈ Up, (e z).2 ≠ 0 := by
    intro z hz he
    exact (ne_of_gt hz.2.1) ((hpair z (hUs (hUp hz))).mp he)
  have hUmne : ∀ z ∈ Um, (e z).2 ≠ 0 := by
    intro z hz he
    exact (ne_of_lt hz.2.2) ((hpair z (hUs (hUm hz))).mp he)
  have hr2 : 0 < r / 2 := by positivity
  have hpr : (p, r / 2) ∈ Up := ⟨hpW, hr2, by linarith⟩
  have hmr : (p, -(r / 2)) ∈ Um := ⟨hpW, by linarith, neg_lt_zero.mpr hr2⟩
  let sp := sign (e (p, r / 2)).2
  let sm := sign (e (p, -(r / 2))).2
  have hsp : sp ≠ 0 := sign_ne_zero.mpr (hUpne _ hpr)
  have hplus : ∀ z ∈ Up, sign (e z).2 = sp := by
    intro z hz
    exact normal_sign_eq_of_preconnected hUpc (fun z => (e z).2)
      (e.continuousOn.mono (hUp.trans hUs)).snd hUpne hz hpr
  have hminus : ∀ z ∈ Um, sign (e z).2 = sm := by
    intro z hz
    exact normal_sign_eq_of_preconnected hUmc (fun z => (e z).2)
      (e.continuousOn.mono (hUm.trans hUs)).snd hUmne hz hmr
  have hcases : ∀ z ∈ U,
      sign (e z).2 = 0 ∨ sign (e z).2 = sp ∨ sign (e z).2 = sm := by
    intro z hz
    rcases lt_trichotomy z.2 0 with hn | he | hpz
    · exact Or.inr (Or.inr (hminus z ⟨hz.1, hz.2.1, hn⟩))
    · exact Or.inl (sign_eq_zero_iff.mpr ((hpair z (hUs hz)).mpr he))
    · exact Or.inr (Or.inl (hplus z ⟨hz.1, hpz, hz.2.2⟩))
  have hbase : ((e (p, (0 : ℝ))).1, (0 : ℝ)) = e (p, 0) := by
    apply Prod.ext
    · rfl
    · exact ((hpair (p, 0) hp).mpr rfl).symm
  have hvertical : IsOpen
      ((fun a : ℝ => ((e (p, 0)).1, a)) ⁻¹' (e '' U)) :=
    (e.isOpen_image_of_subset_source hU hUs).preimage
      (continuous_const.prodMk continuous_id)
  have hzero : (0 : ℝ) ∈ (fun a : ℝ => ((e (p, 0)).1, a)) ⁻¹' (e '' U) := by
    change ((e (p, 0)).1, (0 : ℝ)) ∈ e '' U
    rw [hbase]
    exact mem_image_of_mem e hpU
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hvertical 0 hzero
  have hd2 : 0 < d / 2 := by positivity
  have himage (a : ℝ) (ha : |a| < d) : ((e (p, 0)).1, a) ∈ e '' U := by
    apply hdball
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ha
  have hpos : (1 : SignType) = 0 ∨ 1 = sp ∨ 1 = sm := by
    obtain ⟨z, hz, he⟩ := himage (d / 2) (by rw [abs_of_pos hd2]; linarith)
    have h := hcases z hz
    rw [he, sign_pos hd2] at h
    exact h
  have hneg : (-1 : SignType) = 0 ∨ -1 = sp ∨ -1 = sm := by
    obtain ⟨z, hz, he⟩ := himage (-(d / 2)) (by
      rw [abs_neg, abs_of_pos hd2]
      linarith)
    have h := hcases z hz
    rw [he, sign_neg (neg_lt_zero.mpr hd2)] at h
    exact h
  have hflip : sm = -sp := by
    have halgebra : ∀ a b : SignType,
        ((1 : SignType) = 0 ∨ 1 = a ∨ 1 = b) →
        ((-1 : SignType) = 0 ∨ -1 = a ∨ -1 = b) → b = -a := by decide
    exact halgebra sp sm hpos hneg
  refine ⟨sp, hsp, U, hU, hpU, hUs, ?_⟩
  intro z hz
  rcases lt_trichotomy z.2 0 with hn | he | hpz
  · rw [hminus z ⟨hz.1, hz.2.1, hn⟩, hflip, sign_neg hn, mul_neg, mul_one]
  · rw [(hpair z (hUs hz)).mpr he, sign_zero, he, sign_zero, mul_zero]
  · rw [hplus z ⟨hz.1, hpz, hz.2.2⟩, sign_pos hpz, mul_one]



noncomputable def locallyConnectedNormalTransitionSign
    (e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ))
    (hpair : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0)
    (p : {p : P // (p, (0 : ℝ)) ∈ e.source}) : SignType :=
  (exists_normalSignAt_of_locallyConnected e hpair p.val p.property).choose

theorem locallyConnectedNormalTransitionSign_spec
    (e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ))
    (hpair : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0)
    (p : {p : P // (p, (0 : ℝ)) ∈ e.source}) :
    NormalSignAt e p.val (locallyConnectedNormalTransitionSign e hpair p) :=
  (exists_normalSignAt_of_locallyConnected e hpair p.val p.property).choose_spec



theorem locallyConnectedNormalTransitionSign_isLocallyConstant
    (e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ))
    (hpair : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    IsLocallyConstant (locallyConnectedNormalTransitionSign e hpair) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨W, hW, hp, hsign⟩ :=
    (locallyConnectedNormalTransitionSign_spec e hpair p).exists_open
  refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hp, ?_⟩
  intro q hq
  exact (locallyConnectedNormalTransitionSign_spec e hpair q).unique (hsign q.val hq)

end BrownCollar
