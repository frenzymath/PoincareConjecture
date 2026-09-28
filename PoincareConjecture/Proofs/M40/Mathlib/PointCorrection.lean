import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Function Set Filter Metric
open scoped Topology ContDiff NNReal unitInterval

namespace PoincareConjecture.M40

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutoffTranslation (β : E → ℝ) (v : E) (x : E) : E :=
  x + β x • v

theorem cutoffTranslation_eq_self {β : E → ℝ} (v : E) {x : E}
    (hx : β x = 0) : cutoffTranslation β v x = x := by
  simp [cutoffTranslation, hx]

theorem cutoffTranslation_eventuallyEq {β : E → ℝ} (v : E) {x : E}
    (hx : x ∉ tsupport β) : cutoffTranslation β v =ᶠ[𝓝 x] id := by
  filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hx] with y hy
  exact cutoffTranslation_eq_self v (image_eq_zero_of_notMem_tsupport hy)

theorem cutoffTranslation_eq_target {β : E → ℝ} {a b : E}
    (ha : β a = 1) : cutoffTranslation β (b - a) a = b := by
  simp only [cutoffTranslation, ha, one_smul]
  abel

theorem continuous_cutoffTranslation {β : E → ℝ} (hβ : Continuous β) :
    Continuous (fun p : E × E => cutoffTranslation β p.1 p.2) :=
  continuous_snd.add ((hβ.comp continuous_snd).smul continuous_fst)

theorem contDiff_cutoffTranslation {β : E → ℝ} {n : ℕ∞}
    (hβ : ContDiff ℝ n β) (v : E) : ContDiff ℝ n (cutoffTranslation β v) :=
  contDiff_id.add (hβ.smul contDiff_const)

theorem dist_cutoffTranslation_self_le {β : E → ℝ} (v x : E)
    (hβ0 : 0 ≤ β x) (hβ1 : β x ≤ 1) :
    dist (cutoffTranslation β v x) x ≤ ‖v‖ := by
  simp only [cutoffTranslation, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_of_nonneg hβ0]
  exact mul_le_of_le_one_left (norm_nonneg v) hβ1

theorem hasCompactSupport_cutoffTranslation_sub_id {β : E → ℝ}
    (hβ : HasCompactSupport β) (v : E) :
    HasCompactSupport (fun x => cutoffTranslation β v x - x) := by
  simpa only [Pi.smul_def', cutoffTranslation, add_sub_cancel_left] using
    (hβ.smul_right (f' := fun _ => v))

theorem lipschitzWith_cutoff_displacement {β : E → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (v : E) :
    LipschitzWith (L * ‖v‖₊) (fun x => β x • v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_smul, norm_smul]
  have hb : ‖β x - β y‖ ≤ (L : ℝ) * dist x y := by
    simpa only [← dist_eq_norm] using (hβ.dist_le_mul x y)
  calc
    ‖β x - β y‖ * ‖v‖ ≤ ((L : ℝ) * dist x y) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg v)
    _ = ((L * ‖v‖₊ : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

theorem lipschitzWith_cutoffTranslation {β : E → ℝ} {L : ℝ≥0}
    (hβ : LipschitzWith L β) (v : E) :
    LipschitzWith (1 + L * ‖v‖₊) (cutoffTranslation β v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdis := (lipschitzWith_cutoff_displacement hβ v).dist_le_mul x y
  have heq : cutoffTranslation β v x - cutoffTranslation β v y =
      (x - y) + (β x • v - β y • v) := by
    simp only [cutoffTranslation]
    abel
  rw [dist_eq_norm, heq]
  calc
    ‖(x - y) + (β x • v - β y • v)‖ ≤
        ‖x - y‖ + ‖β x • v - β y • v‖ := norm_add_le _ _
    _ ≤ dist x y + ((L * ‖v‖₊ : ℝ≥0) : ℝ) * dist x y := by
      simpa only [← dist_eq_norm] using (add_le_add le_rfl hdis)
    _ = ((1 + L * ‖v‖₊ : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_one]
      ring

theorem fderiv_cutoffTranslation {β : E → ℝ} {x : E}
    (hβ : DifferentiableAt ℝ β x) (v : E) :
    fderiv ℝ (cutoffTranslation β v) x =
      ContinuousLinearMap.id ℝ E + (fderiv ℝ β x).smulRight v := by
  exact ((hasFDerivAt_id x).add (hβ.hasFDerivAt.smul_const v)).fderiv

theorem norm_fderiv_cutoffTranslation_sub_id_le {β : E → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L β) {x : E} (hβ : DifferentiableAt ℝ β x) (v : E) :
    ‖fderiv ℝ (cutoffTranslation β v) x - ContinuousLinearMap.id ℝ E‖ ≤
      (L : ℝ) * ‖v‖ := by
  have hsmul : fderiv ℝ (fun y => β y • v) x = (fderiv ℝ β x).smulRight v :=
    (hβ.hasFDerivAt.smul_const v).fderiv
  rw [fderiv_cutoffTranslation hβ, add_sub_cancel_left, ← hsmul]
  exact norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_cutoff_displacement hL v)

theorem cutoffTranslation_mapsTo_ball {β : E → ℝ} {c v : E} {r R : ℝ}
    (hβ0 : ∀ x, 0 ≤ β x) (hβ1 : ∀ x, β x ≤ 1)
    (hzero : ∀ x, r ≤ dist x c → β x = 0) (hv : ‖v‖ ≤ R - r) :
    MapsTo (cutoffTranslation β v) (ball c R) (ball c R) := by
  intro x hx
  by_cases hxr : dist x c < r
  · have hdist := (dist_triangle (cutoffTranslation β v x) x c).trans
      (add_le_add (dist_cutoffTranslation_self_le v x (hβ0 x) (hβ1 x)) le_rfl)
    change dist (cutoffTranslation β v x) c < R
    linarith
  · simpa only [cutoffTranslation_eq_self v (hzero x (le_of_not_gt hxr))] using hx

def cutoffTranslationHomotopy {β : E → ℝ} (hβ : Continuous β) (v : E) :
    (ContinuousMap.id E).Homotopy
      ⟨cutoffTranslation β v, continuous_id.add (hβ.smul continuous_const)⟩ where
  toFun p := cutoffTranslation β ((p.1 : ℝ) • v) p.2
  continuous_toFun := continuous_snd.add
    ((hβ.comp continuous_snd).smul
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const))
  map_zero_left x := by simp [cutoffTranslation]
  map_one_left x := by
    change cutoffTranslation β ((1 : ℝ) • v) x = cutoffTranslation β v x
    rw [one_smul]

section MetricBound

variable [FiniteDimensional ℝ E]

theorem exists_metric_bound_of_continuous_family
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (N : E × E → ℝ) (hN : ContinuousOn N (U ×ˢ univ))
    (hNpos : ∀ x ∈ K, ∀ w : E, w ≠ 0 → 0 < N (x, w))
    (hNsmul : ∀ x ∈ U, ∀ (c : ℝ) (w : E), N (x, c • w) = |c| * N (x, w))
    (F : E × E → E) (A : E × E → E →L[ℝ] E)
    (hF : Continuous F) (hA : Continuous A)
    (hF0 : ∀ x ∈ K, F (0, x) = x)
    (hA0 : ∀ x ∈ K, A (0, x) = ContinuousLinearMap.id ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : E, ‖v‖ < δ → ∀ x ∈ K,
      F (v, x) ∈ U ∧ ∀ w : E, N (F (v, x), A (v, x) w) ≤ (1 + η) * N (x, w) := by
  have hrange : ∀ᶠ v in 𝓝 (0 : E), ∀ x ∈ K, F (v, x) ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hF.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hF0 x hx]; exact hKU hx))
  have hsphere : ∀ᶠ v in 𝓝 (0 : E), ∀ p ∈ K ×ˢ sphere (0 : E) 1,
      N (F (v, p.1), A (v, p.1) p.2) < (1 + η) * N p := by
    apply (hK.prod (isCompact_sphere (0 : E) 1)).eventually_forall_of_forall_eventually
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    have hw_norm : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    have hw_ne : w ≠ 0 := by
      intro hw0
      simpa only [hw0, norm_zero, zero_ne_one] using hw_norm
    have hFx : F (0, x) ∈ U := by rw [hF0 x hx]; exact hKU hx
    have hleft : ContinuousAt
        (fun p : E × (E × E) => N (F (p.1, p.2.1), A (p.1, p.2.1) p.2.2))
        (0, (x, w)) :=
      (hN.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hFx, mem_univ _⟩)).comp
        (f := fun p : E × (E × E) => (F (p.1, p.2.1), A (p.1, p.2.1) p.2.2))
        ((hF.comp (continuous_fst.prodMk continuous_snd.fst)).continuousAt.prodMk
          ((hA.comp (continuous_fst.prodMk continuous_snd.fst)).clm_apply
            continuous_snd.snd).continuousAt)
    have hright : ContinuousAt
        (fun p : E × (E × E) => (1 + η) * N p.2) (0, (x, w)) :=
      continuousAt_const.mul
        ((hN.continuousAt ((hU.prod isOpen_univ).mem_nhds
          ⟨hKU hx, mem_univ w⟩)).comp
            (f := fun p : E × (E × E) => p.2) continuous_snd.continuousAt)
    apply hleft.eventually_lt hright
    simp only [hF0 x hx, hA0 x hx, ContinuousLinearMap.id_apply]
    nlinarith [hNpos x hx w hw_ne]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hrange.and hsphere)
  refine ⟨δ, hδ, fun v hv x hx => ?_⟩
  have hv' : v ∈ ball (0 : E) δ := by simpa only [mem_ball, dist_zero_right] using hv
  obtain ⟨hr, hs⟩ := hball hv'
  refine ⟨hr x hx, fun w => ?_⟩
  by_cases hw : w = 0
  · have hzero (y : E) (hy : y ∈ U) : N (y, 0) = 0 := by
      simpa only [zero_smul, abs_zero, zero_mul] using hNsmul y hy 0 (0 : E)
    simp only [hw, map_zero, hzero _ (hr x hx), hzero _ (hKU hx), mul_zero, le_refl]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let z : E := ‖w‖⁻¹ • w
    have hz : z ∈ sphere (0 : E) 1 := by
      simp only [z, mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
    have hs' := (hs (x, z) ⟨hx, hz⟩).le
    have hscale : ‖w‖ • z = w := smul_inv_smul₀ hn.ne' w
    calc
      N (F (v, x), A (v, x) w) =
          ‖w‖ * N (F (v, x), A (v, x) z) := by
        conv_lhs => rw [← hscale, map_smul, hNsmul _ (hr x hx), abs_of_pos hn]
      _ ≤ ‖w‖ * ((1 + η) * N (x, z)) := mul_le_mul_of_nonneg_left hs' hn.le
      _ = (1 + η) * N (x, w) := by
        calc
          ‖w‖ * ((1 + η) * N (x, z)) = (1 + η) * (‖w‖ * N (x, z)) := by ring
          _ = (1 + η) * N (x, w) := by
            congr 1
            simpa only [abs_of_pos hn, hscale] using (hNsmul x (hKU hx) ‖w‖ z).symm

theorem exists_cutoffTranslation_metric_bound
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (N : E × E → ℝ) (hN : ContinuousOn N (U ×ˢ univ))
    (hNpos : ∀ x ∈ K, ∀ w : E, w ≠ 0 → 0 < N (x, w))
    (hNsmul : ∀ x ∈ U, ∀ (c : ℝ) (w : E), N (x, c • w) = |c| * N (x, w))
    {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : E, ‖v‖ < δ → ∀ x ∈ K,
      cutoffTranslation β v x ∈ U ∧ ∀ w : E,
        N (cutoffTranslation β v x, fderiv ℝ (cutoffTranslation β v) x w) ≤
          (1 + η) * N (x, w) := by
  let A : E × E → E →L[ℝ] E := fun p =>
    ContinuousLinearMap.id ℝ E + (fderiv ℝ β p.2).smulRight p.1
  have hA : Continuous A := by
    exact continuous_const.add
      (((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
        ((hβ.continuous_fderiv (by simp)).comp continuous_snd)).clm_apply continuous_fst)
  have hAeq (v x : E) : fderiv ℝ (cutoffTranslation β v) x = A (v, x) :=
    fderiv_cutoffTranslation ((hβ.differentiable (by simp)) x) v
  simpa only [← hAeq] using exists_metric_bound_of_continuous_family hU hK hKU
    N hN hNpos hNsmul (fun p => cutoffTranslation β p.1 p.2) A
    (continuous_cutoffTranslation hβ.continuous) hA
    (fun x _ => by simp [cutoffTranslation])
    (fun x _ => by ext w; simp [A]) hη

theorem exists_cutoffTranslation_metric_bound_on
    {U : Set E} (hU : IsOpen U)
    (N : E × E → ℝ) (hN : ContinuousOn N (U ×ˢ univ))
    (hNpos : ∀ x ∈ U, ∀ w : E, w ≠ 0 → 0 < N (x, w))
    (hNsmul : ∀ x ∈ U, ∀ (c : ℝ) (w : E), N (x, c • w) = |c| * N (x, w))
    {β : E → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcβ : HasCompactSupport β) (hsβ : tsupport β ⊆ U) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : E, ‖v‖ < δ → ∀ x ∈ U,
      cutoffTranslation β v x ∈ U ∧ ∀ w : E,
        N (cutoffTranslation β v x, fderiv ℝ (cutoffTranslation β v) x w) ≤
          (1 + η) * N (x, w) := by
  obtain ⟨δ, hδ, hbound⟩ := exists_cutoffTranslation_metric_bound hU hcβ hsβ
    N hN (fun x hx => hNpos x (hsβ hx)) hNsmul hβ hη
  refine ⟨δ, hδ, fun v hv x hx => ?_⟩
  by_cases hxs : x ∈ tsupport β
  · exact hbound v hv x hxs
  · have heq : cutoffTranslation β v x = x :=
      cutoffTranslation_eq_self v (image_eq_zero_of_notMem_tsupport hxs)
    have hderiv : fderiv ℝ (cutoffTranslation β v) x = ContinuousLinearMap.id ℝ E := by
      simpa only [fderiv_id] using (cutoffTranslation_eventuallyEq v hxs).fderiv_eq (𝕜 := ℝ)
    refine ⟨by simpa only [heq] using hx, fun w => ?_⟩
    rw [heq, hderiv, ContinuousLinearMap.id_apply]
    have hnonneg : 0 ≤ N (x, w) := by
      by_cases hw : w = 0
      · have hz : N (x, 0) = 0 := by
          simpa only [zero_smul, abs_zero, zero_mul] using hNsmul x hx 0 (0 : E)
        simp only [hw, hz, le_refl]
      · exact (hNpos x hx w hw).le
    nlinarith

theorem exists_contDiff_pointCorrection_metric
    {U : Set E} (hU : IsOpen U) {b : E} (hb : b ∈ U)
    (N : E × E → ℝ) (hN : ContinuousOn N (U ×ˢ univ))
    (hNpos : ∀ x ∈ U, ∀ w : E, w ≠ 0 → 0 < N (x, w))
    (hNsmul : ∀ x ∈ U, ∀ (c : ℝ) (w : E), N (x, c • w) = |c| * N (x, w))
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ ball b r, ∃ f : C(E, E),
      ContDiff ℝ ∞ f ∧ f a = b ∧ HasCompactSupport (fun x => f x - x) ∧
      (∀ x ∉ U, f x = x) ∧ (∀ x, dist (f x) x ≤ dist a b) ∧
      (∀ x ∈ U, ∀ w : E, N (f x, fderiv ℝ f x w) ≤ (1 + η) * N (x, w)) ∧
      ∃ H : (ContinuousMap.id E).Homotopy f,
        (∀ t : unitInterval, MapsTo (fun x => H (t, x)) U U) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧
          ∀ (t : unitInterval) (x : E), x ∉ K → H (t, x) = x := by
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hb)
  let β : ContDiffBump b := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  have hsβ : tsupport (β : E → ℝ) ⊆ U := by
    rw [β.tsupport_eq]
    exact hRU
  obtain ⟨δ, hδ, hbound⟩ := exists_cutoffTranslation_metric_bound_on hU N hN hNpos
    hNsmul β.contDiff β.hasCompactSupport hsβ hη
  refine ⟨min (R / 2) δ, lt_min (half_pos hR) hδ, fun a ha => ?_⟩
  have ha' : dist a b < min (R / 2) δ := ha
  have hv : ‖b - a‖ < δ := by
    rw [← dist_eq_norm, dist_comm]
    exact ha'.trans_le (min_le_right _ _)
  have hβa : β a = 1 := β.one_of_mem_closedBall
    (ha'.le.trans (min_le_left _ _))
  let f : C(E, E) := ⟨cutoffTranslation β (b - a),
    continuous_id.add (β.continuous.smul continuous_const)⟩
  refine ⟨f, contDiff_cutoffTranslation β.contDiff _, cutoffTranslation_eq_target hβa,
    hasCompactSupport_cutoffTranslation_sub_id β.hasCompactSupport _, ?_, ?_, ?_,
    ⟨cutoffTranslationHomotopy β.continuous (b - a), ?_, tsupport (β : E → ℝ),
      β.hasCompactSupport, hsβ, ?_⟩⟩
  · intro x hx
    exact cutoffTranslation_eq_self _
      (image_eq_zero_of_notMem_tsupport (fun h => hx (hsβ h)))
  · intro x
    change dist (cutoffTranslation β (b - a) x) x ≤ dist a b
    simpa only [← dist_eq_norm, dist_comm] using
      dist_cutoffTranslation_self_le (b - a) x β.nonneg β.le_one
  · intro x hx w
    exact (hbound (b - a) hv x hx).2 w
  · intro t x hx
    have htv : ‖(t : ℝ) • (b - a)‖ < δ := by
      apply lt_of_le_of_lt _ hv
      rw [norm_smul, Real.norm_of_nonneg t.property.1]
      exact mul_le_of_le_one_left (norm_nonneg _) t.property.2
    exact (hbound ((t : ℝ) • (b - a)) htv x hx).1
  · intro t x hx
    exact cutoffTranslation_eq_self _ (image_eq_zero_of_notMem_tsupport hx)

theorem exists_contDiff_pointCorrection_inner
    {U : Set E} (hU : IsOpen U) {b : E} (hb : b ∈ U)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContinuousOn B U)
    (hBpos : ∀ x ∈ U, ∀ w : E, w ≠ 0 → 0 < B x w w)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ ball b r, ∃ f : C(E, E),
      ContDiff ℝ ∞ f ∧ f a = b ∧ HasCompactSupport (fun x => f x - x) ∧
      (∀ x ∉ U, f x = x) ∧ (∀ x, dist (f x) x ≤ dist a b) ∧
      (∀ x ∈ U, ∀ w : E,
        B (f x) (fderiv ℝ f x w) (fderiv ℝ f x w) ≤ (1 + η) ^ 2 * B x w w) ∧
      ∃ H : (ContinuousMap.id E).Homotopy f,
        (∀ t : unitInterval, MapsTo (fun x => H (t, x)) U U) ∧
        ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧
          ∀ (t : unitInterval) (x : E), x ∉ K → H (t, x) = x := by
  let N : E × E → ℝ := fun p => Real.sqrt (B p.1 p.2 p.2)
  have hN : ContinuousOn N (U ×ˢ univ) :=
    (((hB.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn).sqrt
  have hNpos : ∀ x ∈ U, ∀ w : E, w ≠ 0 → 0 < N (x, w) :=
    fun x hx w hw => Real.sqrt_pos.mpr (hBpos x hx w hw)
  have hNsmul : ∀ x ∈ U, ∀ (c : ℝ) (w : E), N (x, c • w) = |c| * N (x, w) := by
    intro x _ c w
    simp only [N, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  obtain ⟨r, hr, hcor⟩ := exists_contDiff_pointCorrection_metric hU hb N hN hNpos hNsmul hη
  refine ⟨r, hr, fun a ha => ?_⟩
  obtain ⟨f, hf, hfa, hfc, hfout, hfclose, hfbound, H, hH, hK⟩ := hcor a ha
  refine ⟨f, hf, hfa, hfc, hfout, hfclose, ?_, H, hH, hK⟩
  intro x hx w
  have hfx : f x ∈ U := by
    have hh : H (1, x) ∈ U := hH 1 hx
    simpa only [H.apply_one] using hh
  have hBnonneg (y : E) (hy : y ∈ U) (z : E) : 0 ≤ B y z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hBpos y hy z hz).le
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) (hfbound x hx w)
  dsimp only [N] at hsq
  simpa only [← pow_two, mul_pow,
    Real.sq_sqrt (hBnonneg (f x) hfx (fderiv ℝ f x w)),
    Real.sq_sqrt (hBnonneg x hx w)] using hsq

end MetricBound

end PoincareConjecture.M40
