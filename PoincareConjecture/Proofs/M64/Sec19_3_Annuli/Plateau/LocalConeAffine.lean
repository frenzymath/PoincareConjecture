import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.DiskGreenRescaling
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakRescaling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture



def m64ConeNormalize (a : LoopPlane) (r : ℝ) (p : LoopPlane) : LoopPlane :=
  r⁻¹ • (p - a)



theorem m64ConeNormalize_continuous (a : LoopPlane) (r : ℝ) :
    Continuous (m64ConeNormalize a r) :=
  (continuous_id.sub continuous_const).const_smul r⁻¹



theorem m64ConeNormalize_affine (a : LoopPlane) (r : ℝ) :
    (fun p : LoopPlane => -(r⁻¹ • a) + r⁻¹ • p) = m64ConeNormalize a r := by
  funext p
  dsimp only [m64ConeNormalize]
  module



theorem m64ConeNormalize_apply (a : LoopPlane) {r : ℝ} (hr : 0 < r) (p : LoopPlane) :
    m64ConeNormalize a r (a + r • p) = p := by
  rw [m64ConeNormalize, add_sub_cancel_left, inv_smul_smul₀ hr.ne']



theorem m64ConeNormalize_preimage_ball (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    m64ConeNormalize a r ⁻¹' ball 0 1 = ball a r := by
  ext p
  simp only [mem_preimage, m64ConeNormalize, mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul, div_lt_iff₀ hr, one_mul]



theorem m64ConeNormalize_memLp
    {E : Type*} [NormedAddCommGroup E] {f : LoopPlane → E} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (ball (0 : LoopPlane) 1)))
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    MemLp (f ∘ m64ConeNormalize a r) p (volume.restrict (ball a r)) := by
  have hh := M60.suAffine_memLp hf (-(r⁻¹ • a)) (inv_pos.mpr hr)
  rw [m64ConeNormalize_affine, m64ConeNormalize_preimage_ball a hr] at hh
  change MemLp (f ∘ (fun x : LoopPlane => -(r⁻¹ • a) + r⁻¹ • x)) p
    (volume.restrict (ball a r)) at hh
  rwa [m64ConeNormalize_affine] at hh



theorem m64ConeNormalize_quasiMeasurePreserving (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (m64ConeNormalize a r)
      (volume.restrict (ball a r)) (volume.restrict (ball (0 : LoopPlane) 1)) := by
  have hmap := M60.suAffine_map_restrict (-(r⁻¹ • a)) (inv_pos.mpr hr)
    (ball (0 : LoopPlane) 1)
  rw [m64ConeNormalize_affine, m64ConeNormalize_preimage_ball a hr] at hmap
  refine ⟨(m64ConeNormalize_continuous a r).measurable, ?_⟩
  rw [hmap]
  exact Measure.smul_absolutelyContinuous



theorem m64ConeAffine_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : LoopPlane → E) (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    (∫ p in ball a r, f p) =
      ∫ z in ball (0 : LoopPlane) 1, r ^ 2 • f (a + r • z) := by
  have hh := m64Affine_integral_vector f a hr (ball (0 : LoopPlane) 1)
  rw [M60.suAffine_image_ball a hr, mul_one] at hh
  exact hh.symm



theorem m64ConeNormalize_integral_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : LoopPlane → E) (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    (∫ p in ball a r, f (m64ConeNormalize a r p)) =
      r ^ 2 • ∫ z in ball (0 : LoopPlane) 1, f z := by
  rw [m64ConeAffine_integral _ a hr, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change r ^ 2 • f (m64ConeNormalize a r (a + r • z)) = r ^ 2 • f z
    rw [m64ConeNormalize_apply a hr]

end PoincareConjecture
