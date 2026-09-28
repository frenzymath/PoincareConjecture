import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Analysis.SpecialFunctions.SmoothTransition









set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower





theorem exists_inner_reference_filling_field :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let Q : Set E2 := Metric.closedBall 0 (1 / 2)
    let B : ℝ := 17 / 16 + 1 / 8192
    let Bplus : ℝ := 17 / 16 + 2 / 8192
    ∀ (vmin : E2) (m a : ℝ) (e0 : OpenPartialHomeomorph E2 E2),
      m = U vmin →
      0 < a → m + 9 * a ^ 2 < B →
      e0 0 = vmin → Metric.closedBall 0 (3 * a) ⊆ e0.source →
      e0.target ⊆ Metric.ball 0 (1 / 2) →
      ContDiffOn ℝ ∞ e0 e0.source →
      ContDiffOn ℝ ∞ e0.symm e0.target →
      (∀ p ∈ e0.source, U (e0 p) = m + ‖p‖ ^ 2) →
      (∀ v ∈ Q, U v ≤ m + 9 * a ^ 2 → v ∈ e0.target) →
      (∀ v ∈ Q, fderiv ℝ U v = 0 ↔ v = vmin) →
      ∃ (beta : ℝ → ℝ) (W : E2 → E2),
        ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
        tsupport beta ⊆ Ioo (m + a ^ 2 / 4) Bplus ∧
        (∀ b ∈ Icc (m + a ^ 2 / 2) B, beta b = 1) ∧
        (∀ b : ℝ, beta b ∈ Icc 0 1) ∧
        ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
        tsupport W ⊆ Metric.ball (0 : E2) (1 / 2) \ {vmin} ∧
        (∀ v ∈ Metric.ball (0 : E2) (1 / 2),
          fderiv ℝ U v (W v) = beta (U v)) ∧
        (∀ p : E2, a ^ 2 / 2 ≤ ‖p‖ ^ 2 → ‖p‖ ^ 2 ≤ 2 * a ^ 2 →
          W (e0 p) = fderiv ℝ e0 p ((2 * ‖p‖ ^ 2)⁻¹ • p)) := by
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let Q : Set E2 := closedBall 0 (1 / 2)
  let D : Set E2 := ball 0 (1 / 2)
  let B : ℝ := 17 / 16 + 1 / 8192
  let Bplus : ℝ := 17 / 16 + 2 / 8192
  dsimp only
  intro vmin m a e0 hm ha haB hzero hsource htarget he hei hquad hfull hcrit
  change m = U vmin at hm
  change m + 9 * a ^ 2 < B at haB
  change ∀ p ∈ e0.source, U (e0 p) = m + ‖p‖ ^ 2 at hquad
  change ∀ v ∈ Q, U v ≤ m + 9 * a ^ 2 → v ∈ e0.target at hfull
  change ∀ v ∈ Q, fderiv ℝ U v = 0 ↔ v = vmin at hcrit
  obtain ⟨hUs, _, _, _, _, _, v0, _hv0, _hlo, _hhi, _hc0, _hu0,
    _hi0, _hgap, hsub⟩ := inner_reference_convex_geometry
  change ContDiffOn ℝ ∞ U (ball (0 : E2) 1) at hUs
  change ∀ b ≤ Bplus, IsCompact {v : E2 | v ∈ Q ∧ U v ≤ b} ∧
    {v : E2 | v ∈ Q ∧ U v ≤ b} ⊆ D at hsub
  have hDU : D ⊆ ball (0 : E2) 1 := by
    intro v hv
    rw [mem_ball_zero_iff] at hv ⊢
    linarith only [hv]
  have hU : ContDiffOn ℝ ∞ U D := hUs.mono hDU
  have hUc : Continuous U :=
    ((continuous_norm.pow 2).add
      ((continuous_const.sub (continuous_norm.pow 2)).sqrt)).add
        ((EuclideanSpace.proj (0 : Fin 2)).continuous.div_const 32)
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hBB : B < Bplus := by norm_num [B, Bplus]
  let V : Set E2 := D \ {vmin}
  let O : Set E2 := e0.target \ {vmin}
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hO : IsOpen O := e0.open_target.sdiff isClosed_singleton
  have hpn (v : E2) (hv : v ∈ O) : e0.symm v ≠ 0 := by
    intro hz
    have hh := e0.right_inv hv.1
    rw [hz, hzero] at hh
    exact hv.2 hh.symm
  let X0 : E2 → E2 := fun v =>
    fderiv ℝ e0 (e0.symm v) ((2 * ‖e0.symm v‖ ^ 2)⁻¹ • e0.symm v)
  have hX0 : ContDiffOn ℝ ∞ X0 O := by
    have hp : ContDiffOn ℝ ∞ e0.symm O := hei.mono sdiff_subset
    have hd := (he.fderiv_of_isOpen e0.open_source (by simp)).comp hp
      (fun v hv => e0.map_target hv.1)
    exact hd.clm_apply
      (((contDiffOn_const.mul (hp.norm_sq ℝ)).inv
        (fun v hv => mul_ne_zero (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.mpr
          (hpn v hv))))).smul hp)
  have hX0speed (v : E2) (hv : v ∈ O) : fderiv ℝ U v (X0 v) = 1 := by
    let p := e0.symm v
    have hp : p ∈ e0.source := e0.map_target hv.1
    have hpn0 : p ≠ 0 := hpn v hv
    have hquadratic : (fun y => U (e0 y)) =ᶠ[𝓝 p] fun y => m + ‖y‖ ^ 2 := by
      filter_upwards [e0.open_source.mem_nhds hp] with y hy
      exact hquad y hy
    have hUp := (hU.contDiffAt (isOpen_ball.mem_nhds
      (htarget (e0.map_source hp)))).differentiableAt (by simp)
    have hep := (he.contDiffAt (e0.open_source.mem_nhds hp)).differentiableAt (by simp)
    have hd := (hUp.hasFDerivAt.comp p hep.hasFDerivAt).congr_of_eventuallyEq
      hquadratic.symm
    have heq := hd.unique ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add m)
    have hvalue := congrArg (fun A : E2 →L[ℝ] ℝ => A ((2 * ‖p‖ ^ 2)⁻¹ • p)) heq
    rw [ContinuousLinearMap.comp_apply, e0.right_inv hv.1] at hvalue
    change fderiv ℝ U v (X0 v) = _ at hvalue
    rw [hvalue]
    rw [smul_apply, innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [two_smul]
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hpn0)]
    ring
  have hgn (v : E2) (hv : v ∈ V) : gradient U v ≠ 0 := by
    intro hz
    have hd : fderiv ℝ U v = 0 := by
      rw [← toDual_gradient, hz, map_zero]
    exact hv.2 ((hcrit v (ball_subset_closedBall hv.1)).mp hd)
  let X1 : E2 → E2 := fun v => (‖gradient U v‖ ^ 2)⁻¹ • gradient U v
  have hg : ContDiffOn ℝ ∞ (gradient U) V :=
    (contDiffOn_gradient_of_isOpen isOpen_ball U hU).mono sdiff_subset
  have hX1 : ContDiffOn ℝ ∞ X1 V :=
    ((hg.norm_sq ℝ).inv (fun v hv => pow_ne_zero _ (norm_ne_zero_iff.mpr (hgn v hv)))).smul hg
  have hX1speed (v : E2) (hv : v ∈ V) : fderiv ℝ U v (X1 v) = 1 := by
    change fderiv ℝ U v ((‖gradient U v‖ ^ 2)⁻¹ • gradient U v) = 1
    rw [map_smul, smul_eq_mul, ← inner_gradient_left, real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hgn v hv)))
  let K0 : Set E2 := {v : E2 | v ∈ Q ∧ U v ≤ m + 4 * a ^ 2}
  have hK0 : IsCompact K0 := (hsub (m + 4 * a ^ 2) (by linarith only [haB, hBB, ha2])).1
  have hK0T : K0 ⊆ e0.target := fun v hv =>
    hfull v hv.1 (by linarith only [hv.2, ha2])
  obtain ⟨chi0, hc0, _hc0c, hc0s, hc0near, _hc0range⟩ :=
    exists_compact_smooth_cutoff hK0 e0.open_target hK0T
  let eta : E2 → ℝ := fun v => 1 - Real.smoothTransition ((U v - (m + 2 * a ^ 2)) / a ^ 2)
  have heta : ContDiffOn ℝ ∞ eta D :=
    contDiffOn_const.sub (Real.smoothTransition.contDiff.comp_contDiffOn
      ((hU.sub contDiffOn_const).div_const _))
  let alpha : E2 → ℝ := fun v => chi0 v * eta v
  have halpha : ContDiffOn ℝ ∞ alpha V := hc0.contDiffOn.mul (heta.mono sdiff_subset)
  have hY : ContDiffOn ℝ ∞ (fun v => alpha v • X0 v) V := by
    intro v hv
    by_cases hc : v ∈ tsupport chi0
    · exact ((halpha.contDiffAt (hV.mem_nhds hv)).smul
        (hX0.contDiffAt (hO.mem_nhds ⟨hc0s hc, hv.2⟩))).contDiffWithinAt
    · have heq : (fun y => alpha y • X0 y) =ᶠ[𝓝 v] fun _ => (0 : E2) := by
        filter_upwards [(isClosed_tsupport chi0).isOpen_compl.mem_nhds hc] with y hy
        simp only [alpha, image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  let X : E2 → E2 := fun v => alpha v • X0 v + (1 - alpha v) • X1 v
  have hX : ContDiffOn ℝ ∞ X V := hY.add ((contDiffOn_const.sub halpha).smul hX1)
  have hXspeed (v : E2) (hv : v ∈ V) : fderiv ℝ U v (X v) = 1 := by
    by_cases hc : chi0 v = 0
    · simp only [X, alpha, hc, zero_mul, zero_smul, sub_zero, one_smul,
        zero_add, hX1speed v hv]
    · have hvO : v ∈ O := ⟨hc0s (subset_tsupport chi0 hc), hv.2⟩
      simp only [X, map_add, map_smul, smul_eq_mul, hX0speed v hvO,
        hX1speed v hv, mul_one]
      ring
  have hinterval : Icc (m + a ^ 2 / 2) B ⊆ Ioo (m + a ^ 2 / 4) Bplus := by
    intro b hb
    exact ⟨by linarith only [hb.1, ha2], hb.2.trans_lt hBB⟩
  obtain ⟨beta, hb, hbc, hbs, hbnear, hbrange⟩ :=
    exists_compact_smooth_cutoff isCompact_Icc isOpen_Ioo hinterval
  have hbOne (b : ℝ) (hbI : b ∈ Icc (m + a ^ 2 / 2) B) : beta b = 1 :=
    subset_of_mem_nhdsSet hbnear hbI
  let K : Set E2 := Q ∩ U ⁻¹' tsupport beta
  have hK : IsCompact K := (isCompact_closedBall (0 : E2) (1 / 2)).inter_right
    ((isClosed_tsupport beta).preimage hUc)
  have hKV : K ⊆ V := by
    intro v hv
    have hi := hbs hv.2
    refine ⟨(hsub Bplus le_rfl).2 ⟨hv.1, hi.2.le⟩, ?_⟩
    intro heq
    have heq' : v = vmin := heq
    rw [heq', ← hm] at hi
    linarith only [hi.1, ha2]
  obtain ⟨chi1, hc1, hc1c, hc1s, hc1near, _hc1range⟩ :=
    exists_compact_smooth_cutoff hK hV hKV
  let W : E2 → E2 := fun v => chi1 v • (beta (U v) • X v)
  have hW : ContDiff ℝ ∞ W := contDiff_cutoff_smul hV chi1 hc1 hc1s _
    ((hb.comp_contDiffOn (hU.mono sdiff_subset)).smul hX)
  refine ⟨beta, W, hb, hbc, hbs, hbOne, hbrange, hW, hc1c.smul_right,
    (tsupport_smul_subset_left chi1 _).trans hc1s, ?_, ?_⟩
  · intro v hv
    change fderiv ℝ U v (W v) = beta (U v)
    by_cases hz : beta (U v) = 0
    · simp only [W, hz, zero_smul, smul_zero, map_zero]
    · have hvK : v ∈ K := ⟨ball_subset_closedBall hv, subset_tsupport beta hz⟩
      have hc : chi1 v = 1 := subset_of_mem_nhdsSet hc1near hvK
      simp only [W, hc, one_smul, map_smul, smul_eq_mul, hXspeed v (hKV hvK), mul_one]
  · intro p hplo hphi
    have hpS : p ∈ e0.source := by
      apply hsource
      rw [mem_closedBall_zero_iff]
      nlinarith only [hphi, ha, norm_nonneg p]
    have hpQ : e0 p ∈ Q := ball_subset_closedBall (htarget (e0.map_source hpS))
    have hpval := hquad p hpS
    have h0 : chi0 (e0 p) = 1 := subset_of_mem_nhdsSet hc0near
      ⟨hpQ, by linarith only [hpval, hphi, ha2]⟩
    have het : eta (e0 p) = 1 := by
      have hn : (U (e0 p) - (m + 2 * a ^ 2)) / a ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith only [hpval, hphi]) ha2.le
      simp only [eta, Real.smoothTransition.zero_of_nonpos hn, sub_zero]
    have hbval : beta (U (e0 p)) = 1 := hbOne _
      ⟨by linarith only [hpval, hplo], by linarith only [hpval, hphi, ha2, haB]⟩
    have hpK : e0 p ∈ K := ⟨hpQ, subset_tsupport beta (by
      change beta (U (e0 p)) ≠ 0
      rw [hbval]
      norm_num)⟩
    have h1 : chi1 (e0 p) = 1 := subset_of_mem_nhdsSet hc1near hpK
    change W (e0 p) = _
    simp only [W, X, alpha, h0, het, hbval, h1, one_mul, one_smul,
      sub_self, zero_smul, add_zero, X0, e0.left_inv hpS]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
