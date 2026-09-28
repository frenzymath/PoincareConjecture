import PoincareConjecture.Proofs.M35.CapGeometry.RoundSurfaceRicci
import PoincareConjecture.Definitions.M27ProductModels
import PoincareConjecture.Proofs.M13.ContractionTransport
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)

private theorem ancient_zero_derivative_constant {f : ℝ → ℝ}
    (hf : ∀ t ≤ 0, HasDerivWithinAt f 0 (Iic 0) t) {t : ℝ} (ht : t ≤ 0) :
    f t = f 0 := by
  have hd (s : ℝ) (hs : s ∈ Iic (0 : ℝ)) :
      HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Iic 0) s :=
    hasFDerivWithinAt_iff_hasDerivWithinAt.mpr (hf s hs)
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd (fun _ _ => norm_zero.le) (show (0 : ℝ) ∈ Iic 0 by norm_num) ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

theorem round_factor_metric_time_affine
    (g : ℝ → RiemannianMetric 2 E2) (D : ∀ t, LeviCivitaData (g t))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (g t) (D t))
    (heq : ∀ t ≤ 0, ∀ x u v : E2,
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (-2 * (D t).ricci x u v) (Iic 0) t)
    (t : ℝ) (ht : t ≤ 0) (x u v : E2) :
    (g t).inner x u v = (g 0).inner x u v - 2 * t * (D 0).ricci x u v := by
  classical
  let e : E2 := EuclideanSpace.single 0 1
  have he : e ≠ 0 := by simp [e]
  let a (s : ℝ) := (g s).inner 0 e e
  have ha (s : ℝ) : 0 < a s := (g s).pos 0 e he
  have hratio (y p q : E2) (s : ℝ) (hs : s ≤ 0) :
      HasDerivWithinAt (fun z => (g z).inner y p q / a z) 0 (Iic 0) s := by
    obtain ⟨c, _hc, hsec⟩ := hround s hs
    have hf := heq s hs y p q
    have hA := heq s hs 0 e e
    rw [surface_ricci_of_sectional (D s) y c (hsec y)] at hf
    rw [surface_ricci_of_sectional (D s) 0 c (hsec 0)] at hA
    have hquot := hf.div hA (ha s).ne'
    dsimp only [a]
    convert! hquot using 1
    ring
  have hscale (s : ℝ) (hs : s ≤ 0) (y p q : E2) :
      (g s).inner y p q = (a s / a 0) * (g 0).inner y p q := by
    have h := ancient_zero_derivative_constant (hratio y p q) hs
    have hcross := (div_eq_div_iff (ha s).ne' (ha 0).ne').mp h
    rw [div_mul_eq_mul_div, eq_div_iff (ha 0).ne']
    simpa only [mul_comm] using hcross
  have hricci (s : ℝ) (hs : s ≤ 0) (y p q : E2) :
      (D s).ricci y p q = (D 0).ricci y p q := by
    have hhom : MetricHomothety (g 0) (g s) (Diffeomorph.refl (𝓡 2) E2 ∞)
        (a s / a 0) := by
      intro z b c
      rw [Diffeomorph.coe_refl, mfderiv_id]
      exact hscale s hs z b c
    have h := M13.homothety_ricci_eq (g 0) (g s) (Diffeomorph.refl (𝓡 2) E2 ∞)
      (a s / a 0) (div_pos (ha s) (ha 0)) hhom (D 0) (D s) y p q
    rw [Diffeomorph.coe_refl, mfderiv_id] at h
    exact h
  have hzero (s : ℝ) (hs : s ≤ 0) :
      HasDerivWithinAt (fun z => (g z).inner x u v + 2 * z * (D 0).ricci x u v)
        0 (Iic 0) s := by
    have hf := heq s hs x u v
    rw [hricci s hs] at hf
    have hlin := (((hasDerivAt_id s).const_mul 2).mul_const
      ((D 0).ricci x u v)).hasDerivWithinAt (s := Iic 0)
    convert! hf.add hlin using 1
    ring
  have h := ancient_zero_derivative_constant hzero ht
  simp only [mul_zero, zero_mul, add_zero] at h
  linarith only [h]

end PoincareConjecture.M35
