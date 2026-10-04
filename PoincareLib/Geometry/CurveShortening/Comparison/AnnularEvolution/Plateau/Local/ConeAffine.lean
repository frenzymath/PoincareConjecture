import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Disk.GreenRescaling
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Weak.Rescaling

/-!
# Affine transport between the unit disk and an actual local disk

The normalization map preserves local Lp data and null sets. The
two-dimensional Jacobian is retained explicitly in the integral formula.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareMT

/-- Positive affine disk normalization subtracts the center and divides by the radius. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def m64ConeNormalize (a : LoopPlane) (r : ℝ) (p : LoopPlane) : LoopPlane :=
  r⁻¹ • (p - a)

/-- The literal affine disk normalization is continuous. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeNormalize_continuous (a : LoopPlane) (r : ℝ) :
    Continuous (m64ConeNormalize a r) :=
  (continuous_id.sub continuous_const).const_smul r⁻¹

/-- Rewrite disk normalization in the affine form used by weak transport. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeNormalize_affine (a : LoopPlane) (r : ℝ) :
    (fun p : LoopPlane => -(r⁻¹ • a) + r⁻¹ • p) = m64ConeNormalize a r := by
  funext p
  dsimp only [m64ConeNormalize]
  module

/-- Positive-radius normalization inverts the literal affine disk parametrization. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeNormalize_apply (a : LoopPlane) {r : ℝ} (hr : 0 < r) (p : LoopPlane) :
    m64ConeNormalize a r (a + r • p) = p := by
  rw [m64ConeNormalize, add_sub_cancel_left, inv_smul_smul₀ hr.ne']

/-- Positive-radius normalization pulls back the unit disk to the actual centered disk.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeNormalize_preimage_ball (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    m64ConeNormalize a r ⁻¹' ball 0 1 = ball a r := by
  ext p
  simp only [mem_preimage, m64ConeNormalize, mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul, div_lt_iff₀ hr, one_mul]

/-- Affine disk normalization transports actual Lp integrability. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

/-- Positive-radius disk normalization preserves null sets for the restricted measures.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeNormalize_quasiMeasurePreserving (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (m64ConeNormalize a r)
      (volume.restrict (ball a r)) (volume.restrict (ball (0 : LoopPlane) 1)) := by
  have hmap := M60.suAffine_map_restrict (-(r⁻¹ • a)) (inv_pos.mpr hr)
    (ball (0 : LoopPlane) 1)
  rw [m64ConeNormalize_affine, m64ConeNormalize_preimage_ball a hr] at hmap
  refine ⟨(m64ConeNormalize_continuous a r).measurable, ?_⟩
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

/-- Affine integration on a physical disk retains its exact squared-radius Jacobian. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ConeAffine_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : LoopPlane → E) (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    (∫ p in ball a r, f p) =
      ∫ z in ball (0 : LoopPlane) 1, r ^ 2 • f (a + r • z) := by
  have hh := m64Affine_integral_vector f a hr (ball (0 : LoopPlane) 1)
  rw [M60.suAffine_image_ball a hr, mul_one] at hh
  exact hh.symm

/-- Integrating a normalized disk field gives the exact squared-radius scaling. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

end PoincareMT
