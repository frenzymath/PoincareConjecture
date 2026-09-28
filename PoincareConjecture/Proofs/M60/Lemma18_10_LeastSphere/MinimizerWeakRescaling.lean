import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRescaling
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Pointwise ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def suAffineHomeomorph (a : Plane) {s : ℝ} (hs : 0 < s) : Plane ≃ₜ Plane :=
  (Homeomorph.smulOfNeZero s hs.ne').trans (Homeomorph.addLeft a)

theorem suAffine_image_ball (a : Plane) {s : ℝ} (hs : 0 < s) (R : ℝ) :
    (fun z : Plane => a + s • z) '' Metric.ball 0 R = Metric.ball a (s * R) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs.le]
    exact mul_lt_mul_of_pos_left
      (by simpa only [Metric.mem_ball, dist_zero_right] using hw) hs
  · intro hz
    refine ⟨s⁻¹ • (z - a), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      have h := mul_lt_mul_of_pos_left
        (show ‖z - a‖ < s * R by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
        (inv_pos.mpr hs)
      simpa only [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] using h
    · change a + s • (s⁻¹ • (z - a)) = z
      rw [smul_inv_smul₀ hs.ne']
      abel

theorem suAffine_preimage_ball (a : Plane) {s : ℝ} (hs : 0 < s) (R : ℝ) :
    (fun z : Plane => a + s • z) ⁻¹' Metric.ball a (s * R) = Metric.ball 0 R := by
  rw [← suAffine_image_ball a hs R]
  exact Set.preimage_image_eq _ (suAffineHomeomorph a hs).injective

theorem suAffine_map_volume (a : Plane) {s : ℝ} (hs : 0 < s) :
    (volume : Measure Plane).map (fun x => a + s • x) =
      ENNReal.ofReal ((s ^ 2)⁻¹) • volume := by
  change Measure.map ((fun x : Plane => a + x) ∘ (fun x : Plane => s • x)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_addHaar_smul volume hs.ne',
    Measure.map_smul, (measurePreserving_add_left (volume : Measure Plane) a).map_eq]
  have hdim : Module.finrank ℝ Plane = 2 := by simp
  rw [hdim, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s))]

theorem suAffine_map_restrict (a : Plane) {s : ℝ} (hs : 0 < s) (O : Set Plane) :
    (volume.restrict ((fun x : Plane => a + s • x) ⁻¹' O)).map
      (fun x => a + s • x) = ENNReal.ofReal ((s ^ 2)⁻¹) • volume.restrict O := by
  have h := (suAffineHomeomorph a hs).toMeasurableEquiv.restrict_map volume O
  change ((volume : Measure Plane).map (fun x => a + s • x)).restrict O =
    (volume.restrict ((fun x : Plane => a + s • x) ⁻¹' O)).map (fun x => a + s • x) at h
  rw [suAffine_map_volume a hs, Measure.restrict_smul] at h
  exact h.symm

theorem suAffine_memLp {E : Type*} [NormedAddCommGroup E]
    {O : Set Plane} {u : Plane → E} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict O)) (a : Plane) {s : ℝ} (hs : 0 < s) :
    MemLp (fun x => u (a + s • x)) p
      (volume.restrict ((fun x : Plane => a + s • x) ⁻¹' O)) := by
  have h : MemLp u p ((volume.restrict ((fun x : Plane => a + s • x) ⁻¹' O)).map
      (fun x => a + s • x)) := by
    rw [suAffine_map_restrict a hs O]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map (by fun_prop)

theorem suAffine_weakPartial {O : Set Plane} {u p : Plane → ℝ} {i : Fin 2}
    (hw : HasWeakPartialDeriv i p u O) (a : Plane) {s : ℝ} (hs : 0 < s) :
    HasWeakPartialDeriv i (fun x => s * p (a + s • x))
      (fun x => u (a + s • x)) ((fun x : Plane => a + s • x) ⁻¹' O) := by
  intro φ hφ hφc hφO
  let e := suAffineHomeomorph a hs
  let S := (fun x : Plane => a + s • x) ⁻¹' O
  let ψ : Plane → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := by
    change ContDiff ℝ ∞ (fun x => φ (s⁻¹ • (-a + x)))
    exact hφ.comp ((contDiff_const.add contDiff_id).const_smul s⁻¹)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph e.symm
  have hψO : tsupport ψ ⊆ O := by
    rw [show ψ = φ ∘ e.symm from rfl, tsupport_comp_eq_preimage]
    intro x hx
    have h := hφO hx
    change e (e.symm x) ∈ O at h
    simpa using h
  have hcomp : (fun y => ψ (a + s • y)) = φ := by
    ext y
    exact congrArg φ (e.symm_apply_apply y)
  have hd (y : Plane) : s * fderiv ℝ ψ (a + s • y) (EuclideanSpace.single i 1) =
      fderiv ℝ φ y (EuclideanSpace.single i 1) := by
    have h := suRescale_fderiv ψ a s y
    rw [hcomp] at h
    exact (congrArg (fun A : Plane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) h).symm
  have himage : (fun y : Plane => a + s • y) '' S = O := by
    exact Set.image_preimage_eq _ e.surjective
  have hleft : s * (∫ y in S,
      u (a + s • y) * fderiv ℝ φ y (EuclideanSpace.single i 1)) =
      ∫ x in O, u x * fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    calc
      _ = ∫ y in S, s ^ 2 *
          (u (a + s • y) * fderiv ℝ ψ (a + s • y) (EuclideanSpace.single i 1)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only; rw [← hd y]; ring
      _ = _ := by
        simpa only [himage] using suRescale_integral
          (fun x => u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) a hs S
  have hright : s * (∫ y in S, (s * p (a + s • y)) * φ y) =
      ∫ x in O, p x * ψ x := by
    calc
      _ = ∫ y in S, s ^ 2 * (p (a + s • y) * ψ (a + s • y)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only; rw [congrFun hcomp y]; ring
      _ = _ := by
        simpa only [himage] using suRescale_integral (fun x => p x * ψ x) a hs S
  apply (mul_left_cancel₀ hs.ne')
  rw [mul_neg, hleft, hright]
  exact hw ψ hψ hψc hψO

end PoincareConjecture.M60

end
