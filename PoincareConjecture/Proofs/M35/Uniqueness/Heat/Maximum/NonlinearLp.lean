import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.FieldEmbedding
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearCauchy









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)

theorem nonlinearField_memLp (T : V × Z → ℝ) (hT : Continuous T)
    (hT0 : ∀ x, T (x, 0) = 0) {C : ℝ}
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (f : Lp Z 2 (volume : Measure V)) :
    MemLp (fun x => T (x, f x)) 2 (volume : Measure V) := by
  apply ((Lp.memLp f).norm.const_mul C).mono'
  · exact hT.comp_aestronglyMeasurable
      (continuous_id.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f))
  · exact Filter.Eventually.of_forall fun x => by
      simpa only [hT0, sub_zero] using hLip x (f x) 0

def nonlinearFieldLp (T : V × Z → ℝ) (hT : Continuous T)
    (hT0 : ∀ x, T (x, 0) = 0) {C : ℝ}
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (f : Lp Z 2 (volume : Measure V)) : Lp ℝ 2 (volume : Measure V) :=
  (nonlinearField_memLp T hT hT0 hLip f).toLp (fun x => T (x, f x))

theorem nonlinearFieldLp_coe (T : V × Z → ℝ) (hT : Continuous T)
    (hT0 : ∀ x, T (x, 0) = 0) {C : ℝ}
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (f : Lp Z 2 (volume : Measure V)) :
    nonlinearFieldLp T hT hT0 hLip f =ᵐ[volume] fun x => T (x, f x) :=
  (nonlinearField_memLp T hT hT0 hLip f).coeFn_toLp

theorem nonlinearFieldLp_continuous (T : V × Z → ℝ) (hT : Continuous T)
    (hT0 : ∀ x, T (x, 0) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖) :
    Continuous (nonlinearFieldLp T hT hT0 hLip) := by
  apply (show LipschitzWith ⟨C, hC⟩ (nonlinearFieldLp T hT hT0 hLip) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm, dist_eq_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (nonlinearFieldLp T hT hT0 hLip f)
      (nonlinearFieldLp T hT hT0 hLip g), Lp.coeFn_sub f g,
    nonlinearFieldLp_coe T hT hT0 hLip f,
    nonlinearFieldLp_coe T hT hT0 hLip g] with x hs hfg hf hg
  simp only [hs, hfg, hf, hg, Pi.sub_apply]
  exact hLip x (f x) (g x)

theorem nonlinearFieldLp_schwartz (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T)
    (hT0 : ∀ x, T (x, 0) = 0) {C : ℝ}
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (X : 𝓢(V, Z)) (hc : HasCompactSupport X) :
    nonlinearFieldLp T hT.continuous hT0 hLip (X.toLp 2 volume) =
      (nonlinearTestSchwartz T hT hT0 X hc).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [nonlinearFieldLp_coe T hT.continuous hT0 hLip (X.toLp 2 volume),
    X.coeFn_toLp 2 volume, (nonlinearTestSchwartz T hT hT0 X hc).coeFn_toLp 2 volume]
    with x hx hX htest
  rw [hx, hX, htest]
  rfl

end PoincareConjecture.M35.Uniqueness.Heat
