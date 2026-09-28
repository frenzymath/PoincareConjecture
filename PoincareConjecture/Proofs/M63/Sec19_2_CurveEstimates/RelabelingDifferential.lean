import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingIntegrals
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SliceCongruence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) {c d : ℝ → ℝ → M}
  {phi : ℝ → ℝ} {t x : ℝ}

theorem smooth_arcSecondDerivative_comp (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    m62ArcSecondDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) x =
      m62ArcSecondDerivative F d t f (phi x) := by
  have hv : Differentiable ℝ (fun y => (curveSpeed F d t y)⁻¹) :=
    ((M62.speed_contDiff F d hd ht).inv
      (fun y => (M62.speed_pos F d hd ht y).ne')).differentiable (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact arcSecondDerivative_comp F d
    ((hd.spatial_regular t ht).mdifferentiable (by norm_num)) hphi hpos
    (fun y => hf.differentiable (by norm_num) (phi y))
    ((hv (phi x)).mul (hf'.differentiable (by norm_num) (phi x)))

theorem regularized_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) (epsilon : ℝ) :
    m62RegularizedCurvature F c epsilon t x =
      m62RegularizedCurvature F d epsilon t (phi x) := by
  rw [regularizedCurvature_congr_slice F hcd]
  exact regularizedCurvature_comp F d
    ((hd.spatial_regular t ht).mdifferentiable (by norm_num)) hphi hpos
    ((M62.unitTangent_contMDiff F d hd ht (phi x)).mdifferentiableAt (by simp)) epsilon

theorem regularized_eventuallyEq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    (ht : t ∈ Ioo a b) (epsilon : ℝ) :
    (fun s => m62RegularizedCurvature F c epsilon s x) =ᶠ[𝓝 t]
      (fun s => m62RegularizedCurvature F d epsilon s (phi x)) := by
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact regularized_eq_of_relabeling F hd hphi hpos hs (hcd s hs) epsilon

theorem regularized_time_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    {K0 K1 K2 epsilon : ℝ} (hE : M62CurveEstimates F d K0 K1 K2)
    (hepsilon : 0 < epsilon) (ht : t ∈ Ioo a b) :
    DifferentiableAt ℝ (fun s => m62RegularizedCurvature F c epsilon s x) t := by
  have h := (hE.regularized_smooth epsilon hepsilon).contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (phi x, t) ∈ univ ×ˢ Ioo a b from ⟨mem_univ _, ht⟩))
  have htime := (h.comp t (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt
    (by simp)
  exact (htime.hasDerivAt.congr_of_eventuallyEq
    (regularized_eventuallyEq_of_relabeling F hd hphi hpos hcd ht epsilon)).differentiableAt

theorem regularized_bound_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    {K0 K1 K2 epsilon : ℝ} (hE : M62CurveEstimates F d K0 K1 K2)
    (hepsilon : 0 < epsilon) (ht : t ∈ Ioo a b) :
    deriv (fun s => m62RegularizedCurvature F c epsilon s x) t ≤
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c epsilon t) x +
        m62Curvature F c t x ^ 3 +
        m62C1 K0 K1 K2 * (m62RegularizedCurvature F c epsilon t x + 1) := by
  have ht' := Ioo_subset_Icc_self ht
  have hscalar : m62RegularizedCurvature F c epsilon t =
      fun y => m62RegularizedCurvature F d epsilon t (phi y) :=
    funext fun _ => regularized_eq_of_relabeling F hd hphi hpos ht' (hcd t ht') epsilon
  have hf : ContDiff ℝ 2 (m62RegularizedCurvature F d epsilon t) :=
    ((hE.regularized_smooth epsilon hepsilon).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).of_le (by decide)
  have hsecond : m62ArcSecondDerivative F c t (m62RegularizedCurvature F c epsilon t) x =
      m62ArcSecondDerivative F d t (m62RegularizedCurvature F d epsilon t) (phi x) := by
    rw [arcSecondDerivative_congr_slice F (hcd t ht'), hscalar]
    exact smooth_arcSecondDerivative_comp F hd hphi hpos ht' hf
  have hk : m62Curvature F c t x = m62Curvature F d t (phi x) := by
    rw [curvature_congr_slice F (hcd t ht')]
    exact curvature_comp F d
      ((hd.spatial_regular t ht').mdifferentiable (by norm_num)) hphi hpos
      ((M62.unitTangent_contMDiff F d hd ht' (phi x)).mdifferentiableAt (by simp))
  rw [(regularized_eventuallyEq_of_relabeling F hd hphi hpos hcd ht epsilon).deriv_eq,
    hsecond, hk, regularized_eq_of_relabeling F hd hphi hpos ht' (hcd t ht') epsilon]
  exact hE.regularized_bound epsilon hepsilon t ht (phi x)

theorem length_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    m62Length F c t = m62Length F d t :=
  (length_congr_slice F hcd).trans (smooth_length_comp F d hd hphi hpos hshift ht)

theorem totalCurvature_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    m62TotalCurvature F c t = m62TotalCurvature F d t :=
  (totalCurvature_congr_slice F hcd).trans
    (smooth_totalCurvature_comp F d hd hphi hpos hshift ht)

theorem length_derivative_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    {K0 K1 K2 : ℝ} (hE : M62CurveEstimates F d K0 K1 K2)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (m62Length F c)
      (-(∫ y in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F c t y + m62TangentRicci F c t y) * curveSpeed F c t y)) t := by
  have heq : m62Length F c =ᶠ[𝓝 t] m62Length F d := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact length_eq_of_relabeling F hd hphi hpos hshift hs (hcd s hs)
  have hslice := hcd t (Ioo_subset_Icc_self ht)
  have hint : (∫ y in (0 : ℝ)..curvePeriod,
      (m62CurvatureSquared F c t y + m62TangentRicci F c t y) * curveSpeed F c t y) =
      ∫ y in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F d t y + m62TangentRicci F d t y) * curveSpeed F d t y := by
    calc
      _ = ∫ y in (0 : ℝ)..curvePeriod,
          (m62CurvatureSquared F (fun z s => d (phi z) s) t y +
            m62TangentRicci F (fun z s => d (phi z) s) t y) *
              curveSpeed F (fun z s => d (phi z) s) t y := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [curvatureSquared_congr_slice F hslice, tangentRicci_congr_slice F hslice,
          curveSpeed_congr_slice F hslice]
      _ = _ := smooth_lengthEvolutionIntegral_comp F d hd hphi hpos hshift ht
  rw [hint]
  exact (hE.length_derivative t ht).congr_of_eventuallyEq heq

theorem total_curvature_integral_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (hcd : ∀ r ∈ Icc a b, ∀ y, c y r = d (phi y) r)
    {K0 K1 K2 : ℝ} (hE : M62CurveEstimates F d K0 K1 K2)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    m62TotalCurvature F c t - m62TotalCurvature F c s ≤
      ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
        m62C1 K0 K1 K2 * m62Length F c r := by
  have hL (r : ℝ) (hr : r ∈ Icc a b) :=
    length_eq_of_relabeling F hd hphi hpos hshift hr (hcd r hr)
  have hTheta (r : ℝ) (hr : r ∈ Icc a b) :=
    totalCurvature_eq_of_relabeling F hd hphi hpos hshift hr (hcd r hr)
  rw [hTheta t ht, hTheta s hs]
  calc
    _ ≤ ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F d r +
        m62C1 K0 K1 K2 * m62Length F d r := hE.total_curvature_integral s t hs ht hst
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hst] at hr
      have hr' : r ∈ Icc a b := ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
      dsimp only
      rw [hTheta r hr', hL r hr']

end PoincareConjecture.M63
