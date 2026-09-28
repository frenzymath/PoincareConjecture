import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityInverseChart
import PoincareConjecture.Proofs.M60.Mathlib.ChartApproximation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64_exists_continuous_extension {n : ℕ} {K : Set LoopPlane}
    (hK : IsClosed K) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hu : ContinuousOn u K) :
    ∃ v : LoopPlane → EuclideanSpace ℝ (Fin n), Continuous v ∧ EqOn v u K := by
  let : TietzeExtension (EuclideanSpace ℝ (Fin n)) := TietzeExtension.of_homeo
    (Module.finBasis ℝ (EuclideanSpace ℝ (Fin n))).equivFun.toContinuousLinearEquiv.toHomeomorph
  let uK : C(K, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun p => u p, continuousOn_iff_continuous_domRestrict.mp hu⟩
  obtain ⟨v, hv⟩ := uK.exists_restrict_eq hK
  exact ⟨v, v.continuous, fun p hp => ContinuousMap.congr_fun hv ⟨p, hp⟩⟩

theorem m64_affine_variation_compact_range {n : ℕ}
    {S : Set LoopPlane} (hS : IsCompact S)
    {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hu : ContinuousOn u S) (hp : ContinuousOn phi S)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsOpen T) (huT : MapsTo u S T) :
    ∃ (delta : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))), 0 < delta ∧
      IsCompact K ∧ K ⊆ T ∧
      ∀ t : ℝ, |t| < delta → MapsTo (fun p => u p + t • phi p) S K := by
  have hKu : IsCompact (u '' S) := hS.image_of_continuousOn hu
  obtain ⟨eta, heta, hmargin⟩ := hKu.exists_cthickening_subset_open hT
    (by rintro _ ⟨p, hp, rfl⟩; exact huT hp)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hp
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨eta / B, Metric.cthickening eta (u '' S), div_pos heta hB,
    hKu.cthickening, hmargin, ?_⟩
  intro t ht p hpS
  apply Metric.mem_cthickening_of_dist_le _ (u p) _ _ (mem_image_of_mem _ hpS)
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hCB : ‖phi p‖ ≤ B := (hC p hpS).trans (by dsimp [B]; linarith [le_max_left C 0])
  exact (mul_le_mul_of_nonneg_left hCB (abs_nonneg t)).trans
    (le_of_lt ((lt_div_iff₀ hB).mp ht))

theorem m64WeakPartial_add {O : Set LoopPlane} {i : Fin 2}
    {u v W Z : LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict O)) (hv : MemLp v 2 (volume.restrict O))
    (hW : MemLp W 2 (volume.restrict O)) (hZ : MemLp Z 2 (volume.restrict O))
    (hw : HasWeakPartialDeriv i W u O) (hz : HasWeakPartialDeriv i Z v O) :
    HasWeakPartialDeriv i (fun p => W p + Z p) (fun p => u p + v p) O := by
  intro phi hp hc hs
  have hm := (hp.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc
    ).mono_measure (Measure.restrict_le_self (s := O))
  have hdm := (((hp.continuous_fderiv (by simp)).clm_apply continuous_const
    ).memLp_of_hasCompactSupport (μ := volume) (p := 2)
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))
    ).mono_measure (Measure.restrict_le_self (s := O))
  simp only [add_mul]
  have hl := integral_add (hu.integrable_mul hdm) (hv.integrable_mul hdm)
  have hr := integral_add (hW.integrable_mul hm) (hZ.integrable_mul hm)
  simp only [Pi.mul_apply] at hl hr
  rw [hl, hr, hw phi hp hc hs, hz phi hp hc hs]
  ring

theorem m64WeakPartial_const_mul {O : Set LoopPlane} {i : Fin 2}
    {u W : LoopPlane → ℝ} (hw : HasWeakPartialDeriv i W u O) (t : ℝ) :
    HasWeakPartialDeriv i (fun p => t * W p) (fun p => t * u p) O := by
  intro phi hp hc hs
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hw phi hp hc hs, mul_neg]

theorem m64_affine_weak_coordinates {n : ℕ}
    {u phi : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ}
    (hu : ContinuousOn u (Metric.closedBall a R)) (hp : ContDiff ℝ ∞ phi)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j)
      (Metric.ball a R)) (t : ℝ) :
    ContinuousOn (fun p => u p + t • phi p) (Metric.closedBall a R) ∧
      (∀ i, MemLp (fun p => W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1)) 2
        (volume.restrict (Metric.ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i
        (fun p => (W i p + t • fderiv ℝ phi p (EuclideanSpace.single i 1)) j)
        (fun p => (u p + t • phi p) j) (Metric.ball a R) := by
  have hm := m64MemLp_on_ball_of_continuous_closedBall hu 2
  have hpm := m64MemLp_on_ball_of_continuous_closedBall hp.continuous.continuousOn 2
    (a := a) (R := R)
  have hdm (i : Fin 2) := m64MemLp_on_ball_of_continuous_closedBall
    ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn 2
      (a := a) (R := R) (u := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))
  refine ⟨hu.add (hp.continuous.const_smul t).continuousOn,
    (fun i => (hW i).add ((hdm i).const_smul t)), ?_⟩
  intro i j
  let P := EuclideanSpace.proj (𝕜 := ℝ) j
  have hweak : HasWeakPartialDeriv i
      (fun p => P (fderiv ℝ phi p (EuclideanSpace.single i 1))) (P ∘ phi)
      (Metric.ball a R) := by
    have h := HasWeakPartialDeriv.of_contDiff (Ω := Metric.ball a R) Metric.isOpen_ball
      ((P.contDiff.comp hp).of_le (m := 1) (by simp)) (i := i)
    simpa only [fderiv_comp _ P.differentiableAt (hp.differentiable (by simp) _),
      P.fderiv, ContinuousLinearMap.comp_apply] using h
  exact m64WeakPartial_add (P.comp_memLp' hm)
    ((P.comp_memLp' hpm).const_mul t) (P.comp_memLp' (hW i))
    ((P.comp_memLp' (hdm i)).const_mul t) (hw i j) (m64WeakPartial_const_mul hweak t)

end PoincareConjecture
