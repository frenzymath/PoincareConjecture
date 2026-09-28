import PoincareConjecture.Proofs.M14.Mathlib.QuadraticTaylorBound
import PoincareConjecture.Proofs.M14.Mathlib.QuadraticActionComparison
import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyStationarity
import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyActionComparison
import PoincareConjecture.Proofs.M08.ChartEulerRegularity











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped NNReal intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private noncomputable local instance dualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance trilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance trilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace





theorem quadratic_short_time_minimality {a b m M : ℝ} (hab : a ≤ b) (hm : 0 < m)
    {S : Set E} (hS : Convex ℝ S) (K : ℝ≥0)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContinuousOn B (Icc a b ×ˢ S)) (hV : ContinuousOn V (Icc a b ×ˢ S))
    (hDB : ContinuousOn DB (Icc a b ×ˢ S)) (hDV : ContinuousOn DV (Icc a b ×ˢ S))
    (hBd : ∀ s ∈ Icc a b, ∀ z ∈ S,
      HasFDerivWithinAt (fun q => B (s, q)) (DB (s, z)) S z)
    (hVd : ∀ s ∈ Icc a b, ∀ z ∈ S,
      HasFDerivWithinAt (fun q => V (s, q)) (DV (s, z)) S z)
    (hBLip : ∀ s ∈ Icc a b, LipschitzOnWith K (fun z => B (s, z)) S)
    (hDBLip : ∀ s ∈ Icc a b, LipschitzOnWith K (fun z => DB (s, z)) S)
    (hDVLip : ∀ s ∈ Icc a b, LipschitzOnWith K (fun z => DV (s, z)) S)
    (hsym : ∀ z ∈ Icc a b ×ˢ S, ∀ v w : E, B z v w = B z w v)
    (hpos : ∀ z ∈ Icc a b ×ˢ S, ∀ v : E, m * ‖v‖ ^ 2 ≤ B z v v)
    (u v : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (humem : MapsTo u (Icc a b) S) (hspeed : ∀ s ∈ Icc a b, ‖v s‖ ≤ M)
    (hud : ∀ s ∈ Ioo a b, HasDerivAt u (v s) s)
    (heuler : ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (v r))
        (M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (v s)) s)
    (hshort : 0 < m / 4 -
      ((K : ℝ) * M ^ 2 / 2 + K + ((K : ℝ) * M) ^ 2 / m) * (b - a) ^ 2)
    (z r : ℝ → E) (hz : ContinuousOn z (Icc a b)) (hzmem : MapsTo z (Icc a b) S)
    (hzd : ∀ s ∈ Ioo a b, HasDerivAt z (r s) s)
    (hr : MemLp r 2 (volume.restrict (Icc a b))) (ha : z a = u a) (hb : z b = u b)
    (hg : IntervalIntegrable (fun s => B (s, z s) (r s) (r s) / 2 + V (s, z s)) volume a b) :
    (∫ s in a..b, B (s, u s) (v s) (v s) / 2 + V (s, u s)) ≤
        ∫ s in a..b, B (s, z s) (r s) (r s) / 2 + V (s, z s) ∧
      ((∫ s in a..b, B (s, z s) (r s) (r s) / 2 + V (s, z s)) ≤
          ∫ s in a..b, B (s, u s) (v s) (v s) / 2 + V (s, u s) →
        EqOn z u (Icc a b)) := by
  let w := fun s => z s - u s
  let P := fun s => M08.chartMomentumVector (B (s, u s)) (v s)
  let Q := fun s => M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (v s)
  let L := fun s => inner ℝ (Q s) (w s) + inner ℝ (P s) (deriv w s)
  let β := (K : ℝ) * M ^ 2 / 2 + K + ((K : ℝ) * M) ^ 2 / m
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hgraph := continuousOn_id.prodMk hu
  have hmap : MapsTo (fun s => (s, u s)) (Icc a b) (Icc a b ×ˢ S) :=
    fun _ hs => ⟨hs, humem hs⟩
  have hBc := hB.comp hgraph hmap
  have hVc := hV.comp hgraph hmap
  have hP : ContinuousOn P (Icc a b) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn (hBc.clm_apply hv)
  have hQ : ContinuousOn Q (Icc a b) :=
    M08.chartForceVector_continuousOn (hDB.comp hgraph hmap) (hDV.comp hgraph hmap) hv
  have hw : ContinuousOn w (Icc a b) := hz.sub hu
  have hwd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt w (r s - v s) s :=
    (hzd s hs).sub (hud s hs)
  have hwdiff : DifferentiableOn ℝ w (Ioo a b) :=
    fun s hs => (hwd s hs).differentiableAt.differentiableWithinAt
  have hvLp : MemLp v 2 (volume.restrict (Icc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm (hv.aestronglyMeasurable measurableSet_Icc)).mpr
    have hi : IntervalIntegrable (fun s => ‖v s‖ ^ 2) volume a b :=
      ((continuous_pow 2).comp_continuousOn hv.norm).intervalIntegrable_of_Icc hab
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  have hd : MemLp (deriv w) 2 (volume.restrict (Icc a b)) := by
    have heq : (r - v) =ᵐ[volume.restrict (Icc a b)] deriv w := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hwd s hs).deriv.symm
    exact (memLp_congr_ae heq).mp (hr.sub hvLp)
  have hwa : w a = 0 := sub_eq_zero.mpr ha
  have hwb : w b = 0 := sub_eq_zero.mpr hb
  obtain ⟨hL, hstationary⟩ :=
    integral_momentum_variation_eq_zero hab P Q w hP hQ hw heuler hwdiff hd hwa hwb
  have hf : IntervalIntegrable (fun s => B (s, u s) (v s) (v s) / 2 + V (s, u s))
      volume a b :=
    ((((hBc.clm_apply hv).clm_apply hv).div_const 2).add hVc).intervalIntegrable_of_Icc hab
  have hlinear (s : ℝ) : L s = DB (s, u s) (w s) (v s) (v s) / 2 +
      B (s, u s) (v s) (deriv w s) + DV (s, u s) (w s) := by
    dsimp only [L, P, Q]
    rw [real_inner_comm _ (M08.chartForceVector _ _ _), M08.chartForceVector_inner,
      real_inner_comm _ (M08.chartMomentumVector _ _), M08.chartMomentumVector_inner]
    ring
  have hpoint (s : ℝ) (hs : s ∈ Ioo a b) :
      m / 4 * ‖deriv w s‖ ^ 2 - β * ‖w s‖ ^ 2 ≤
        (B (s, z s) (r s) (r s) / 2 + V (s, z s)) -
          (B (s, u s) (v s) (v s) / 2 + V (s, u s)) - L s := by
    have hsC := Ioo_subset_Icc_self hs
    have hremB := norm_sub_sub_linear_le_sq hS (hBd s hsC) (hDBLip s hsC)
      (humem hsC) (hzmem hsC)
    have hremV := norm_sub_sub_linear_le_sq hS (hVd s hsC) (hDVLip s hsC)
      (humem hsC) (hzmem hsC)
    have hpot : -((K : ℝ) * ‖w s‖ ^ 2) ≤
        V (s, z s) - V (s, u s) - DV (s, u s) (w s) :=
      (abs_le.mp (by simpa only [Real.norm_eq_abs] using hremV)).1
    have h := quadratic_action_remainder_lower_bound
      (B (s, u s)) (B (s, z s)) (DB (s, u s) (w s)) (v s) (r s - v s) (w s)
      (V (s, u s)) (V (s, z s)) (DV (s, u s) (w s)) m K M hm K.coe_nonneg
      (hspeed s hsC) (hsym _ ⟨hsC, hzmem hsC⟩ _ _) (hpos _ ⟨hsC, hzmem hsC⟩ _)
      ((hBLip s hsC).norm_sub_le (hzmem hsC) (humem hsC)) hremB hpot
    rw [hlinear, (hwd s hs).deriv]
    rw [show v s + (r s - v s) = r s by abel] at h
    exact h
  have hgap := finite_energy_action_gap hab hβ hf hg hL hstationary hw hwdiff hd hwb hpoint
  have he : 0 ≤ ∫ s in a..b, ‖deriv w s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg ‖deriv w s‖)
  refine ⟨?_, ?_⟩
  · have hnonneg := mul_nonneg hshort.le he
    exact sub_nonneg.mp (hnonneg.trans hgap)
  · intro haction s hs
    have hwzero := finite_energy_action_eq_of_gap_nonpos hab hβ hshort hf hg hL
      hstationary hw hwdiff hd hwb hpoint haction s hs
    exact sub_eq_zero.mp hwzero

end PoincareConjecture.M14
