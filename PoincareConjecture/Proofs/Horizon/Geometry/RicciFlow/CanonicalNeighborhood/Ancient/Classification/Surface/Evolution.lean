import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Endpoint
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

private theorem round_scalar_hasDerivAt
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    {s : ℝ} (hs : s < 0) (x : M) :
    HasDerivAt (fun t => (F.connection t).scalarCurvature x)
      (((F.connection s).scalarCurvature x) ^ 2) s := by
  have he := F.hasDerivAt_scalarCurvature_surface
    (show s ∈ interior (Iic (0 : ℝ)) by simpa only [interior_Iic, mem_Iio] using hs) x
  obtain ⟨c, _, hc⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (hround s hs.le)
  have hfun : (F.connection s).scalarCurvature = fun _ => c := funext hc
  have hlap : (F.connection s).laplacian (F.connection s).scalarCurvature x = 0 := by
    rw [hfun]
    simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const]
  simpa only [hlap, zero_add] using he

private theorem eq_terminal_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hderiv : ∀ s < 0, HasDerivAt f 0 s)
    (hcont : ContinuousOn f (Iic 0)) {t : ℝ} (ht : t ≤ 0) : f t = f 0 := by
  have hconst : EqOn f (fun _ => f (-1)) (Iio 0) := by
    intro s hs
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hderiv z hz).deriv) hs (by norm_num)
  have hext := hconst.of_subset_closure hcont continuousOn_const
    Iio_subset_Iic_self (by rw [closure_Iio])
  exact (hext ht).trans (hext (show (0 : ℝ) ∈ Iic 0 by simp)).symm

theorem inv_scalarCurvature_eq_terminal_sub_time_of_round
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    (t : ℝ) (ht : t ≤ 0) (x : M) :
    ((F.connection t).scalarCurvature x)⁻¹ =
      ((F.connection 0).scalarCurvature x)⁻¹ - t := by
  let R : ℝ → ℝ := fun s => (F.connection s).scalarCurvature x
  have hne (s : ℝ) (hs : s ≤ 0) : R s ≠ 0 := by
    obtain ⟨c, hc, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (hround s hs)
    exact ne_of_gt (show 0 < R s by change 0 < (F.connection s).scalarCurvature x; rw [he x]; exact hc)
  have hd (s : ℝ) (hs : s < 0) : HasDerivAt (fun z => (R z)⁻¹ + z) 0 s := by
    have he := ((round_scalar_hasDerivAt F hround hs x).inv (hne s hs.le)).add
      (hasDerivAt_id s)
    change HasDerivAt (fun z => (R z)⁻¹ + z) (-(R s) ^ 2 / (R s) ^ 2 + 1) s at he
    simpa only [neg_div, div_self (pow_ne_zero 2 (hne s hs.le)), neg_add_cancel] using he
  have hc : ContinuousOn (fun z => (R z)⁻¹ + z) (Iic 0) :=
    ((F.continuousOn_scalarCurvature_ancient_surface x).inv₀ hne).add continuousOn_id
  have he := eq_terminal_of_hasDerivAt_zero hd hc ht
  simpa only [add_zero] using eq_sub_iff_add_eq.mpr he

theorem inner_eq_terminal_scalar_scale_of_round
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    (t : ℝ) (ht : t ≤ 0) (x : M) (v w : TangentSpace (𝓡 2) x) :
    (F.metric t).inner x v w =
      (1 - (F.connection 0).scalarCurvature x * t) * (F.metric 0).inner x v w := by
  let R : ℝ → ℝ := fun s => (F.connection s).scalarCurvature x
  let f : ℝ → ℝ := fun s => (F.metric s).inner x v w
  have hd (s : ℝ) (hs : s < 0) : HasDerivAt (fun z => R z * f z) 0 s := by
    have he := (round_scalar_hasDerivAt F hround hs x).mul
      ((F.equation s hs.le x v w).hasDerivAt (Iic_mem_nhds hs))
    rw [(F.connection s).ricci_eq_half_scalarCurvature_mul_inner] at he
    convert he using 1 <;> first | rfl | ring
  have hc : ContinuousOn (fun z => R z * f z) (Iic 0) :=
    (F.continuousOn_scalarCurvature_ancient_surface x).mul
      (Poincare.Geometry.RicciFlow.Harnack.metric_inner_contDiffOn_time F x v w).continuousOn
  have he := eq_terminal_of_hasDerivAt_zero hd hc ht
  obtain ⟨r, hr, hzero⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (hround 0 le_rfl)
  obtain ⟨s, hs, htime⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (hround t ht)
  have hi := F.inv_scalarCurvature_eq_terminal_sub_time_of_round hround t ht x
  change (F.connection t).scalarCurvature x * f t =
    (F.connection 0).scalarCurvature x * f 0 at he
  rw [hzero x, htime x] at hi he
  rw [hzero x]
  change f t = (1 - r * t) * f 0
  calc
    f t = s⁻¹ * (s * f t) := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    _ = (r⁻¹ - t) * (r * f 0) := by rw [he, hi]
    _ = (1 - r * t) * f 0 := by field_simp

end PoincareConjecture.RicciFlow
