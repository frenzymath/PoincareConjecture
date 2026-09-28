import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ParametricInverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set Metric Filter Function MeasureTheory
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)



theorem exists_stackCanonicalBallModel
    (ell r lambdaMinus lambdaPlus : ℝ)
    (hellr : ell < r) (hlm : 0 < lambdaMinus) (hlp : 0 < lambdaPlus)
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let lower := (fun q : UnitTwoSphere =>
      (ell + lambdaMinus * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus
    let upper := (fun q : UnitTwoSphere =>
      (r - lambdaPlus * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ z : ℝ, 0 < deriv g z) ∧ Surjective g ∧
      (∀ z : ℝ, z ≤ -(v0 / 2) → g z = ell + lambdaMinus * z) ∧
      (∀ z : ℝ, v0 / 2 ≤ z → g z = r + lambdaPlus * z) ∧
      ∃ D : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, P) E3 P ∞,
        (∀ x : E3, D x = (g (M (heightCoordinates x)).2, (M (heightCoordinates x)).1)) ∧
        D '' closedBall (0 : E3) 1 ⊆
          Icc (ell - lambdaMinus) (r + lambdaPlus) ×ˢ closedBall (0 : E2) 1 ∧
        ∃ B : BallNeighborhoodChart E3 P,
          B.chart = D.toHomeomorph.toOpenPartialHomeomorph ∧
          B.boundary = lower ∪ (Icc ell r ×ˢ sphere (0 : E2) 1) ∪ upper := by
  let nu := v0 / 2
  have hnu : 0 < nu := div_pos hv0 (by norm_num)
  have hnuv : nu < v0 := by dsimp only [nu]; linarith only [hv0]
  have hnu1 : nu < 1 := hnuv.trans (hv01.trans hv1)
  have hden : 0 < 2 * nu := mul_pos (by norm_num) hnu
  let chi : ℝ → ℝ := fun z =>
    (Real.smoothTransition ((z + nu) / (2 * nu)) + 1 -
      Real.smoothTransition ((nu - z) / (2 * nu))) / 2
  have hchi : ContDiff ℝ ∞ chi := by dsimp only [chi]; fun_prop
  have hchirange (z : ℝ) : 0 ≤ chi z ∧ chi z ≤ 1 := by
    have h1 := Real.smoothTransition.nonneg ((z + nu) / (2 * nu))
    have h2 := Real.smoothTransition.le_one ((z + nu) / (2 * nu))
    have h3 := Real.smoothTransition.nonneg ((nu - z) / (2 * nu))
    have h4 := Real.smoothTransition.le_one ((nu - z) / (2 * nu))
    dsimp only [chi]
    constructor <;> linarith only [h1, h2, h3, h4]
  have hchizero (z : ℝ) (hz : z ≤ -nu) : chi z = 0 := by
    have h1 : (z + nu) / (2 * nu) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by linarith only [hz]) hden.le
    have h2 : 1 ≤ (nu - z) / (2 * nu) := (le_div_iff₀ hden).mpr
      (by linarith only [hz])
    simp only [chi, Real.smoothTransition.zero_of_nonpos h1,
      Real.smoothTransition.one_of_one_le h2]
    norm_num
  have hchione (z : ℝ) (hz : nu ≤ z) : chi z = 1 := by
    have h1 : 1 ≤ (z + nu) / (2 * nu) := (le_div_iff₀ hden).mpr
      (by linarith only [hz])
    have h2 : (nu - z) / (2 * nu) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hz) hden.le
    simp only [chi, Real.smoothTransition.one_of_one_le h1,
      Real.smoothTransition.zero_of_nonpos h2]
    norm_num
  have hchirefl (z : ℝ) : chi (-z) = 1 - chi z := by
    dsimp only [chi]
    rw [show -z + nu = nu - z by ring, sub_neg_eq_add, add_comm nu z]
    ring
  have hchimon : Monotone chi := by
    intro z w hzw
    have h1 : Real.smoothTransition ((z + nu) / (2 * nu)) ≤
        Real.smoothTransition ((w + nu) / (2 * nu)) :=
      Real.smoothTransition.monotone (by gcongr)
    have h2 := Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (sub_le_sub_left hzw nu) hden.le)
    dsimp only [chi]
    linarith only [h1, h2]
  have hchider : ∀ z, 0 ≤ deriv chi z := fun _ => hchimon.deriv_nonneg
  let h0 : ℝ → ℝ := fun z => (1 - chi z) * lambdaMinus + chi z * lambdaPlus
  have hh0 : ContDiff ℝ ∞ h0 :=
    ((contDiff_const.sub hchi).mul contDiff_const).add (hchi.mul contDiff_const)
  have hh0pos (z : ℝ) : 0 < h0 z := by
    have hc := hchirange z
    by_cases hc1 : chi z = 1
    · simpa only [h0, hc1, sub_self, zero_mul, one_mul, zero_add] using hlp
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne hc.2 hc1)) hlm) (mul_nonneg hc.1 hlp.le)
  have hichi : (∫ z in -nu..nu, chi z) = nu := by
    have hrefl : (∫ z in -nu..nu, chi (-z)) = ∫ z in -nu..nu, chi z := by
      simpa only [neg_neg] using
        (intervalIntegral.integral_comp_neg (f := chi) (a := -nu) (b := nu))
    have hsym : (∫ z in -nu..nu, chi (-z)) = 2 * nu - ∫ z in -nu..nu, chi z := by
      calc
        (∫ z in -nu..nu, chi (-z)) = ∫ z in -nu..nu, (1 - chi z) :=
          intervalIntegral.integral_congr (fun z _ => hchirefl z)
        _ = 2 * nu - ∫ z in -nu..nu, chi z := by
          rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
            (hchi.continuous.intervalIntegrable _ _), intervalIntegral.integral_const]
          simp only [smul_eq_mul, mul_one]
          ring
    linarith only [hrefl, hsym]
  have hih0 : (∫ z in -nu..nu, h0 z) = nu * (lambdaMinus + lambdaPlus) := by
    dsimp only [h0]
    rw [intervalIntegral.integral_add (f := fun z => (1 - chi z) * lambdaMinus)
      (g := fun z => chi z * lambdaPlus)
      (((continuous_const.sub hchi.continuous).mul continuous_const).intervalIntegrable _ _)
      ((hchi.continuous.mul continuous_const).intervalIntegrable _ _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
        (hchi.continuous.intervalIntegrable _ _), intervalIntegral.integral_const, hichi]
    simp only [smul_eq_mul]
    ring
  let prim : ℝ → ℝ := fun z => ∫ s in -nu..z, h0 s
  have hprimder (z : ℝ) : HasDerivAt prim (h0 z) z :=
    intervalIntegral.integral_hasDerivAt_right (hh0.continuous.intervalIntegrable _ _)
      hh0.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hh0.continuous.continuousAt
  have hprim : ContDiff ℝ ∞ prim := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun z => (hprimder z).differentiableAt, ?_⟩
    have heq : deriv prim = h0 := funext fun z => (hprimder z).deriv
    rw [heq]
    exact hh0
  let g : ℝ → ℝ := fun z => ell - lambdaMinus * nu + prim z + (r - ell) * chi z
  have hg : ContDiff ℝ ∞ g := (contDiff_const.add hprim).add (contDiff_const.mul hchi)
  have hgder (z : ℝ) : deriv g z = h0 z + (r - ell) * deriv chi z := by
    exact (((hprimder z).const_add (ell - lambdaMinus * nu)).add
      (((hchi.differentiable (by simp)) z).hasDerivAt.const_mul (r - ell))).deriv
  have hgpos (z : ℝ) : 0 < deriv g z := by
    rw [hgder]
    exact add_pos_of_pos_of_nonneg (hh0pos z)
      (mul_nonneg (sub_pos.mpr hellr).le (hchider z))
  have hglow (z : ℝ) (hz : z ≤ -nu) : g z = ell + lambdaMinus * z := by
    have hi : prim z = (z + nu) * lambdaMinus := by
      change (∫ s in -nu..z, h0 s) = _
      calc
        (∫ s in -nu..z, h0 s) = ∫ s in -nu..z, lambdaMinus := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_ge hz] at hs
          simp only [h0, hchizero s hs.2, sub_zero, one_mul, zero_mul, add_zero]
        _ = _ := by simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
    simp only [g, hi, hchizero z hz, mul_zero, add_zero]
    ring
  have hghigh (z : ℝ) (hz : nu ≤ z) : g z = r + lambdaPlus * z := by
    have hi : (∫ s in nu..z, h0 s) = (z - nu) * lambdaPlus := by
      calc
        (∫ s in nu..z, h0 s) = ∫ s in nu..z, lambdaPlus := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hz] at hs
          simp only [h0, hchione s hs.1, sub_self, zero_mul, one_mul, zero_add]
        _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hh0.continuous.intervalIntegrable (-nu) nu) (hh0.continuous.intervalIntegrable nu z)
    have hip : prim z = nu * (lambdaMinus + lambdaPlus) + (z - nu) * lambdaPlus := by
      change (∫ s in -nu..z, h0 s) = _
      rw [← hsplit, hih0, hi]
    simp only [g, hip, hchione z hz, mul_one]
    ring
  have hgmono : StrictMono g := strictMono_of_deriv_pos hgpos
  have hgsurj : Surjective g := by
    intro y
    let zlo := min (-nu) ((y - ell) / lambdaMinus)
    let zhi := max nu ((y - r) / lambdaPlus)
    have hlo : g zlo ≤ y := by
      rw [hglow zlo (min_le_left _ _)]
      have h := (le_div_iff₀ hlm).mp (min_le_right (-nu) ((y - ell) / lambdaMinus))
      dsimp only [zlo]
      nlinarith only [h]
    have hhi : y ≤ g zhi := by
      rw [hghigh zhi (le_max_left _ _)]
      have h := (div_le_iff₀ hlp).mp (le_max_right nu ((y - r) / lambdaPlus))
      dsimp only [zhi]
      nlinarith only [h]
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc
      ((min_le_left (-nu) _).trans ((by linarith only [hnu] : -nu ≤ nu).trans
        (le_max_left nu _))) hg.continuous.continuousOn ⟨hlo, hhi⟩
    exact ⟨z, hz⟩
  refine ⟨g, hg, hgpos, hgsurj, hglow, hghigh, ?_⟩
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  obtain ⟨ha, hapos, _halow, habound, hanear, _hafar, _haeven⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, hbpos, hblow, _hbnear, hbfar, _hbrad⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  change ∀ z, 0 < a z at hapos
  change ∀ z, |z| ≤ v0 → a z = (Real.sqrt (1 - z ^ 2))⁻¹ at hanear
  change ∀ x, 0 < b x at hbpos
  change ∀ x, 1 ≤ b x at hblow
  change ∀ x, rOne ≤ ‖x‖ → b x = 1 at hbfar
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  let N := heightCoordinates.toDiffeomorph.trans
    (flatCapDiffeomorph a b ha hb (fun z => (hapos z).ne') (fun x => (hbpos x).ne'))
  have hN (x : E3) : N x = M (heightCoordinates x) := (hM _).symm
  let V := fiberDiffeomorph (hg.comp contDiff_snd)
    (fun (_ : E2) z => hgpos z) (fun (_ : E2) => hgsurj)
  let D := (N.trans V).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph
  have hD (x : E3) : D x = ((g (M (heightCoordinates x)).2), (M (heightCoordinates x)).1) := by
    change (g (N x).2, (N x).1) = _
    rw [hN]
  obtain ⟨hrefl, hsphereBound⟩ := stackCanonicalModel_reflection_height
    rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
  change ∀ p, M (p.1, -p.2) = ((M p).1, -(M p).2) at hrefl
  change ∀ p, ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 → |(M p).2| ≤ 1 at hsphereBound
  have hsolid (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      ‖(N y).1‖ ≤ 1 ∧ |(N y).2| ≤ 1 := by
    let K := N '' closedBall (0 : E3) 1
    let O := N '' ball (0 : E3) 1
    have hK : IsCompact K := (isCompact_closedBall (0 : E3) 1).image
      N.contMDiff_toFun.continuous
    have hKne : K.Nonempty := ⟨N 0, 0, by simp, rfl⟩
    have hO : IsOpen O := N.toHomeomorph.isOpenMap _ isOpen_ball
    have hOK : O ⊆ K := image_mono ball_subset_closedBall
    have hshift (p : E2 × ℝ) (s : ℝ) : dist (p.1, p.2 + s) p = |s| := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      have heq : p.2 + s - p.2 = s := by ring
      rw [heq, max_eq_right (abs_nonneg s)]
    obtain ⟨pmax, hpmax, hmax⟩ := hK.exists_isMaxOn hKne continuous_snd.continuousOn
    obtain ⟨pmin, hpmin, hmin⟩ := hK.exists_isMinOn hKne continuous_snd.continuousOn
    have hmaxOutside : pmax ∉ O := by
      intro hp
      obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hO pmax hp
      have hnear : (pmax.1, pmax.2 + eps / 2) ∈ ball pmax eps := by
        rw [mem_ball, hshift, abs_of_pos (div_pos heps (by norm_num))]
        linarith only [heps]
      have hle := hmax (hOK (hball hnear))
      change pmax.2 + eps / 2 ≤ pmax.2 at hle
      linarith only [heps, hle]
    have hminOutside : pmin ∉ O := by
      intro hp
      obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hO pmin hp
      have hnear : (pmin.1, pmin.2 + (-eps / 2)) ∈ ball pmin eps := by
        rw [mem_ball, hshift, abs_of_neg (by linarith only [heps] : -eps / 2 < 0)]
        linarith only [heps]
      have hle := hmin (hOK (hball hnear))
      change pmin.2 ≤ pmin.2 + (-eps / 2) at hle
      linarith only [heps, hle]
    have hboundaryBound (p : E2 × ℝ) (hp : p ∈ K) (hout : p ∉ O) : |p.2| ≤ 1 := by
      obtain ⟨x, hx, rfl⟩ := hp
      have hxnorm : ‖x‖ = 1 := by
        apply le_antisymm (mem_closedBall_zero_iff.mp hx)
        by_contra hn
        exact hout ⟨x, mem_ball_zero_iff.mpr (lt_of_not_ge hn), rfl⟩
      let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hxnorm⟩
      rw [hN]
      exact hsphereBound _ (sphere_height_coordinates_sq q)
    have hupper := (abs_le.mp (hboundaryBound pmax hpmax hmaxOutside)).2
    have hlower := (abs_le.mp (hboundaryBound pmin hpmin hminOutside)).1
    have hsq : ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1 := by
      rw [← heightCoordinates_norm_sq]
      nlinarith only [mem_closedBall_zero_iff.mp hy, norm_nonneg y]
    exact ⟨flatCapDiffeomorph_fst_norm_le a b ha hb (fun z => (hapos z).ne')
      (fun x => (hbpos x).ne') hapos habound (heightCoordinates y) hsq,
      abs_le.mpr ⟨hlower.trans (hmin ⟨y, hy, rfl⟩), (hmax ⟨y, hy, rfl⟩).trans hupper⟩⟩
  have hbound : D '' closedBall (0 : E3) 1 ⊆
      Icc (ell - lambdaMinus) (r + lambdaPlus) ×ˢ closedBall (0 : E2) 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hhor, hvert⟩ := hsolid y hy
    have hv := abs_le.mp hvert
    have hlo := hgmono.monotone hv.1
    have hhi := hgmono.monotone hv.2
    rw [hglow (-1) (by linarith only [hnu1]), mul_neg_one, ← sub_eq_add_neg] at hlo
    rw [hghigh 1 hnu1.le, mul_one] at hhi
    exact ⟨⟨hlo, hhi⟩, mem_closedBall_zero_iff.mpr hhor⟩
  have hnear (p : E2 × ℝ) (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 = 1) (hv : |p.2| ≤ nu) :
      M p = ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2) ∧ ‖(M p).1‖ = 1 := by
    have hroot : Real.sqrt (1 - p.2 ^ 2) = ‖p.1‖ := by
      rw [show 1 - p.2 ^ 2 = ‖p.1‖ ^ 2 by linarith only [hp],
        Real.sqrt_sq (norm_nonneg p.1)]
    have hvsq : p.2 ^ 2 < 1 := by
      nlinarith only [sq_abs p.2, abs_nonneg p.2, hv, hnu1, hnu]
    have hrootpos : 0 < Real.sqrt (1 - p.2 ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hvsq)
    have haeq : a p.2 = (Real.sqrt (1 - p.2 ^ 2))⁻¹ := hanear p.2 (hv.trans hnuv.le)
    have hunit : ‖a p.2 • p.1‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hapos p.2), haeq, ← hroot,
        inv_mul_cancel₀ hrootpos.ne']
    have heq : M p = ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2) := by
      rw [hM, hbfar _ (by rw [hunit]; exact hrOne.le), one_mul, haeq]
    exact ⟨heq, by rw [hM]; exact hunit⟩
  have hnative (p : E2 × ℝ) : |p.2| ≤ |(M p).2| := by
    rw [hM, abs_mul, abs_of_pos (hbpos _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hblow (a p.2 • p.1)) (abs_nonneg p.2)
  have hsign (p : E2 × ℝ) : (M p).2 ≤ 0 ↔ p.2 ≤ 0 := by
    rw [hM]
    simpa only [mul_zero] using
      (mul_le_mul_iff_right₀ (hbpos (a p.2 • p.1)) (b := p.2) (c := 0))
  have hcreate (v : ℝ) (hv : |v| ≤ nu) (x : E2) (hx : ‖x‖ = 1) :
      ∃ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 = v ∧
        M (heightCoordinates (q : E3)) = (x, v) := by
    have hrad : 0 < 1 - v ^ 2 := by
      nlinarith only [hv, hnu, hnu1, sq_abs v, abs_nonneg v]
    have hroot : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr hrad
    let y := heightCoordinates.symm (Real.sqrt (1 - v ^ 2) • x, v)
    have hy : ‖y‖ = 1 := by
      have hsq : ‖y‖ ^ 2 = 1 := by
        rw [heightCoordinates_symm_norm_sq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hroot.le, hx, mul_one, Real.sq_sqrt hrad.le]
        ring
      nlinarith only [hsq, norm_nonneg y]
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
    have hcoord : heightCoordinates (q : E3) = (Real.sqrt (1 - v ^ 2) • x, v) :=
      heightCoordinates.apply_symm_apply _
    refine ⟨q, congrArg Prod.snd hcoord, ?_⟩
    have heq := (hnear (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q)
      (by rw [hcoord]; exact hv)).1
    rw [heq, hcoord, smul_smul, inv_mul_cancel₀ hroot.ne', one_smul]
  have hreflection (q : UnitTwoSphere) :
      ∃ qr : UnitTwoSphere,
        (heightCoordinates (qr : E3)).2 = -(heightCoordinates (q : E3)).2 ∧
        M (heightCoordinates (qr : E3)) =
          ((M (heightCoordinates (q : E3))).1, -(M (heightCoordinates (q : E3))).2) := by
    let p := heightCoordinates (q : E3)
    let y := heightCoordinates.symm (p.1, -p.2)
    have hy : ‖y‖ = 1 := by
      have hsq : ‖y‖ ^ 2 = 1 := by
        rw [heightCoordinates_symm_norm_sq, neg_sq]
        exact sphere_height_coordinates_sq q
      nlinarith only [hsq, norm_nonneg y]
    let qr : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
    have hcoord : heightCoordinates (qr : E3) = (p.1, -p.2) :=
      heightCoordinates.apply_symm_apply _
    exact ⟨qr, congrArg Prod.snd hcoord, (congrArg M hcoord).trans (hrefl p)⟩
  have hgleft : g (-nu) = ell - lambdaMinus * nu := by
    rw [hglow (-nu) le_rfl]
    ring
  have hgright : g nu = r + lambdaPlus * nu := hghigh nu le_rfl
  have hcylinder (z : ℝ) (hz : z ∈ Icc (ell - lambdaMinus * nu) (r + lambdaPlus * nu))
      (x : E2) (hx : ‖x‖ = 1) : (z, x) ∈ D '' sphere (0 : E3) 1 := by
    have hzg : z ∈ Icc (g (-nu)) (g nu) := by rw [hgleft, hgright]; exact hz
    obtain ⟨v, hv, heq⟩ := intermediate_value_Icc
      (by linarith only [hnu] : -nu ≤ nu) hg.continuous.continuousOn hzg
    obtain ⟨q, _hqv, hqm⟩ := hcreate v (abs_le.mpr hv) x hx
    refine ⟨(q : E3), q.property, ?_⟩
    rw [hD, hqm]
    exact Prod.ext heq rfl
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let lower := (fun q : UnitTwoSphere =>
    (ell + lambdaMinus * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  let upper := (fun q : UnitTwoSphere =>
    (r - lambdaPlus * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)) '' Qminus
  have hlower : lower ⊆ D '' sphere (0 : E3) 1 := by
    rintro _ ⟨q, hq, rfl⟩
    let p := heightCoordinates (q : E3)
    have hsouth : (M p).2 ≤ 0 := (hsign p).mpr hq
    by_cases hv : (M p).2 ≤ -nu
    · exact ⟨(q : E3), q.property, by rw [hD, hglow _ hv]⟩
    · have hmv : |(M p).2| ≤ nu := abs_le.mpr ⟨(lt_of_not_ge hv).le, hsouth.trans hnu.le⟩
      have hunit := (hnear p (sphere_height_coordinates_sq q) ((hnative p).trans hmv)).2
      apply hcylinder _ ?_ _ hunit
      constructor <;> nlinarith only [lt_of_not_ge hv, hsouth, hlm, hlp, hnu, hellr]
  have hupper : upper ⊆ D '' sphere (0 : E3) 1 := by
    rintro _ ⟨q, hq, rfl⟩
    let p := heightCoordinates (q : E3)
    have hsouth : (M p).2 ≤ 0 := (hsign p).mpr hq
    by_cases hv : (M p).2 ≤ -nu
    · obtain ⟨qr, _hqrh, hqrm⟩ := hreflection q
      refine ⟨(qr : E3), qr.property, ?_⟩
      rw [hD, hqrm, hghigh (-(M p).2) (by linarith only [hv])]
      exact Prod.ext (by ring) rfl
    · have hmv : |(M p).2| ≤ nu := abs_le.mpr ⟨(lt_of_not_ge hv).le, hsouth.trans hnu.le⟩
      have hunit := (hnear p (sphere_height_coordinates_sq q) ((hnative p).trans hmv)).2
      apply hcylinder _ ?_ _ hunit
      constructor <;> nlinarith only [lt_of_not_ge hv, hsouth, hlm, hlp, hnu, hellr]
  have hmiddle : Icc ell r ×ˢ sphere (0 : E2) 1 ⊆ D '' sphere (0 : E3) 1 := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    apply hcylinder z ?_ x (mem_sphere_zero_iff_norm.mp hx)
    constructor <;> nlinarith only [hz.1, hz.2, hlm, hlp, hnu]
  have hboundary : D '' sphere (0 : E3) 1 =
      lower ∪ (Icc ell r ×ˢ sphere (0 : E2) 1) ∪ upper := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      let q : UnitTwoSphere := ⟨y, hy⟩
      let p := heightCoordinates y
      by_cases hlo : (M p).2 ≤ -nu
      · apply Or.inl ∘ Or.inl
        exact ⟨q, (hsign p).mp (hlo.trans (by linarith only [hnu])),
          by rw [hD, hglow _ hlo]⟩
      by_cases hhi : nu ≤ (M p).2
      · obtain ⟨qr, hqrh, hqrm⟩ := hreflection q
        have hpnonneg : 0 ≤ p.2 := by
          by_contra hn
          have hnonpos := (hsign p).mpr (lt_of_not_ge hn).le
          linarith only [hnonpos, hhi, hnu]
        apply Or.inr
        refine ⟨qr, ?_, ?_⟩
        · change (heightCoordinates (qr : E3)).2 ≤ 0
          rw [hqrh]
          exact neg_nonpos.mpr hpnonneg
        · change (r - lambdaPlus * (M (heightCoordinates (qr : E3))).2,
            (M (heightCoordinates (qr : E3))).1) = D y
          rw [hqrm, hD, hghigh _ hhi]
          exact Prod.ext (by ring) rfl
      have hmv : |(M p).2| ≤ nu :=
        abs_le.mpr ⟨(lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩
      have hunit := (hnear p (sphere_height_coordinates_sq q) ((hnative p).trans hmv)).2
      have hzlo := hgmono.monotone (abs_le.mp hmv).1
      have hzhi := hgmono.monotone (abs_le.mp hmv).2
      rw [hgleft] at hzlo
      rw [hgright] at hzhi
      by_cases hzl : g (M p).2 ≤ ell
      · let w := (g (M p).2 - ell) / lambdaMinus
        have hw : w ∈ Icc (-nu) 0 := by
          constructor
          · exact (le_div_iff₀ hlm).mpr (by nlinarith only [hzlo])
          · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzl) hlm.le
        obtain ⟨qr, hqrh, hqrm⟩ := hcreate w
          (abs_le.mpr ⟨hw.1, hw.2.trans hnu.le⟩) (M p).1 hunit
        apply Or.inl ∘ Or.inl
        refine ⟨qr, ?_, ?_⟩
        · change (heightCoordinates (qr : E3)).2 ≤ 0
          rw [hqrh]
          exact hw.2
        · change (ell + lambdaMinus * (M (heightCoordinates (qr : E3))).2,
            (M (heightCoordinates (qr : E3))).1) = D y
          rw [hqrm, hD]
          apply Prod.ext
          · change ell + lambdaMinus * w = g (M p).2
            dsimp only [w]
            field_simp
            ring
          · rfl
      by_cases hzr : r ≤ g (M p).2
      · let w := (r - g (M p).2) / lambdaPlus
        have hw : w ∈ Icc (-nu) 0 := by
          constructor
          · exact (le_div_iff₀ hlp).mpr (by nlinarith only [hzhi])
          · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzr) hlp.le
        obtain ⟨qr, hqrh, hqrm⟩ := hcreate w
          (abs_le.mpr ⟨hw.1, hw.2.trans hnu.le⟩) (M p).1 hunit
        apply Or.inr
        refine ⟨qr, ?_, ?_⟩
        · change (heightCoordinates (qr : E3)).2 ≤ 0
          rw [hqrh]
          exact hw.2
        · change (r - lambdaPlus * (M (heightCoordinates (qr : E3))).2,
            (M (heightCoordinates (qr : E3))).1) = D y
          rw [hqrm, hD]
          apply Prod.ext
          · change r - lambdaPlus * w = g (M p).2
            dsimp only [w]
            field_simp
            ring
          · rfl
      · apply Or.inl ∘ Or.inr
        rw [hD]
        exact ⟨⟨(lt_of_not_ge hzl).le, (lt_of_not_ge hzr).le⟩,
          mem_sphere_zero_iff_norm.mpr hunit⟩
    · exact union_subset (union_subset hlower hmiddle) hupper
  let B : BallNeighborhoodChart E3 P := {
    chart := D.toHomeomorph.toOpenPartialHomeomorph
    closedBall_subset_source := subset_univ _
    smooth := D.contMDiff_toFun.contDiff.contDiffOn
    smooth_symm := D.contMDiff_invFun.contDiff.contDiffOn }
  exact ⟨D, hD, hbound, B, rfl, hboundary⟩

end PoincareConjecture.M25.Topology3D
