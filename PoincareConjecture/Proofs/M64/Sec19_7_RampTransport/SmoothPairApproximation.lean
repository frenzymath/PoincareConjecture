import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ApproximationCollar
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TurningStability
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoinArea
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflection

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

structure SmoothRampAnnulusApproximation
    (P : M62.CircleProductData F circumference) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1) (r epsilon : ℝ) where
  first : ℝ → P.charts.Point
  second : ℝ → P.charts.Point
  first_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ first
  second_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ second
  first_periodic : Function.Periodic first curvePeriod
  second_periodic : Function.Periodic second curvePeriod
  first_ramp : M63IsRampAt P first time
  second_ramp : M63IsRampAt P second time
  first_length_error : |m62Length P.flow (fun y _ => first y) time -
    m62Length P.flow (fun y _ => gamma0 y) time| < epsilon
  second_length_error : |m62Length P.flow (fun y _ => second y) time -
    m62Length P.flow (fun y _ => gamma1 y) time| < epsilon
  first_length_strict : r / 2 < m62Length P.flow (fun y _ => first y) time
  first_turning : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
    m63ArcLength P.flow (fun y _ => first y) time alpha beta ≤ r / 2 →
    m63ArcTotalCurvature P.flow (fun y _ => first y) time alpha beta < (3 / 400 : ℝ)
  annulus : M64Annulus (P.flow.metric time) first second
  area_error : annulus.area < A.area + epsilon

variable [T2Space M] [CompactSpace M]
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι

theorem exists_smooth_ramp_annulus_approximation_of_retraction
    (P : M62.CircleProductData F circumference)
    {time : ℝ} (htime : time ∈ Icc a b)
    {e : P.charts.Point → W} (he : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → P.charts.Point}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 (n + 1)) ∞ rho U)
    (hre : ∀ p, rho (e p) = p)
    {gamma0 gamma1 : ℝ → P.charts.Point}
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod) (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {r : ℝ} (hr : 0 < r)
    (hlength : r ≤ m62Length P.flow (fun y _ => gamma0 y) time)
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength P.flow (fun y _ => gamma0 y) time alpha beta ≤ r →
      m63ArcTotalCurvature P.flow (fun y _ => gamma0 y) time alpha beta < (1 / 200 : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (SmoothRampAnnulusApproximation P time gamma0 gamma1 A r epsilon) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  obtain ⟨delta0, hdelta0, hcollar0⟩ := exists_c2_approximation_collar_tolerance
    P.flow htime he hU heU hrho hre hgamma0 hp0 (M63.ramp_immersed P hramp0)
      (half_pos hepsilon)
  obtain ⟨delta1, hdelta1, hcollar1⟩ := exists_c2_approximation_collar_tolerance
    P.flow htime he hU heU hrho hre hgamma1 hp1 (M63.ramp_immersed P hramp1)
      (half_pos hepsilon)
  obtain ⟨sigma0, hsmooth0, hperiod0, hslope0, hnear0, hlength0, hlong, hturn0⟩ :=
    exists_smooth_ramp_with_turning_margin P htime he hU heU hrho hre
      hgamma0 hp0 hramp0 hr hlength hturn (lt_min hepsilon hdelta0)
  obtain ⟨sigma1, hsmooth1, hperiod1, hslope1, hnear1, harcs1⟩ :=
    exists_smooth_ramp_subarc_approximation P htime he hU heU hrho hre
      hgamma1 hp1 hramp1 (lt_min hepsilon hdelta1)
  have hregular0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 sigma0 :=
    hsmooth0.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hregular1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 sigma1 :=
    hsmooth1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨collar0, harea0⟩ := hcollar0 sigma0 hregular0 hperiod0
    (M63.ramp_immersed P hslope0) (fun x =>
      ⟨(hnear0 x).1.trans_le (min_le_right _ _),
        (hnear0 x).2.1.trans_le (min_le_right _ _),
        (hnear0 x).2.2.trans_le (min_le_right _ _)⟩)
  obtain ⟨collar1, harea1⟩ := hcollar1 sigma1 hregular1 hperiod1
    (M63.ramp_immersed P hslope1) (fun x =>
      ⟨(hnear1 x).1.trans_le (min_le_right _ _),
        (hnear1 x).2.1.trans_le (min_le_right _ _),
        (hnear1 x).2.2.trans_le (min_le_right _ _)⟩)
  obtain ⟨left, _hleftMap, hleftArea⟩ :=
    m64Annulus_join_with_area (m64Annulus_reverse collar0) A
  obtain ⟨B, _hBMap, hBArea⟩ := m64Annulus_join_with_area left collar1
  have hBarea : B.area < A.area + epsilon := by
    rw [hBArea, hleftArea, m64Annulus_reverse_area]
    linarith
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hlength1 : |m62Length P.flow (fun y _ => sigma1 y) time -
      m62Length P.flow (fun y _ => gamma1 y) time| < min epsilon delta1 :=
    (harcs1 0 curvePeriod hperiod (by simp)).1
  exact ⟨{
    first := sigma0
    second := sigma1
    first_smooth := hsmooth0
    second_smooth := hsmooth1
    first_periodic := hperiod0
    second_periodic := hperiod1
    first_ramp := hslope0
    second_ramp := hslope1
    first_length_error := hlength0.trans_le (min_le_left _ _)
    second_length_error := hlength1.trans_le (min_le_left _ _)
    first_length_strict := hlong
    first_turning := hturn0
    annulus := B
    area_error := hBarea }⟩

theorem exists_smooth_ramp_annulus_approximation
    (P : M62.CircleProductData F circumference)
    {time : ℝ} (htime : time ∈ Icc a b)
    {gamma0 gamma1 : ℝ → P.charts.Point}
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod) (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {r : ℝ} (hr : 0 < r)
    (hlength : r ≤ m62Length P.flow (fun y _ => gamma0 y) time)
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength P.flow (fun y _ => gamma0 y) time alpha beta ≤ r →
      m63ArcTotalCurvature P.flow (fun y _ => gamma0 y) time alpha beta < (1 / 200 : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (SmoothRampAnnulusApproximation P time gamma0 gamma1 A r epsilon) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Nonempty P.charts.Point := ⟨gamma0 0⟩
  obtain ⟨dimension, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 (n + 1)) (M := P.charts.Point)
  obtain ⟨U, rho, hU, heU, hrho, hre, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  exact exists_smooth_ramp_annulus_approximation_of_retraction P htime he hU heU hrho hre
    hgamma0 hgamma1 hp0 hp1 hramp0 hramp1 A hr hlength hturn hepsilon

end PoincareConjecture.M64.RampTransport
