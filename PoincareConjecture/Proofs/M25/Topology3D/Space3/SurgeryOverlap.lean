import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood














set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem northSphereCoordinate_circleDirection {q : UnitTwoSphere}
    (hq : q ∈ northSphereDomain) (hx : (heightCoordinates (q : E3)).1 ≠ 0) :
    circleDirection (northSphereCoordinate q) =
      circleDirection (heightCoordinates (q : E3)).1 := by
  let x := (heightCoordinates (q : E3)).1
  have hz : 0 < 1 + (heightCoordinates (q : E3)).2 := by
    change -1 < (heightCoordinates (q : E3)).2 at hq
    linarith
  change circleDirection ((1 + (heightCoordinates (q : E3)).2)⁻¹ • x) =
    circleDirection x
  nth_rw 1 [← circleDirection_norm_smul x]
  rw [smul_smul]
  exact circleDirection_smul (circleDirection x)
    (mul_pos (inv_pos.mpr hz) (norm_pos_iff.mpr hx))



theorem exists_surgery_replacement_overlap
    (a : ℝ → ℝ) (b : E2 → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) (t : ℝ)
    (D : RegularSurgeryData ψ u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRnear : ∀ᶠ w in 𝓝ˢ (sphere (0 : E2) 1),
      R w = surgeryMatchingRadius r (l / k) ‖w‖ • NormedSpace.normalize w)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖)))) :
    ∃ eta > (0 : ℝ), ∀ q : UnitTwoSphere,
      |(heightCoordinates (q : E3)).2| < eta →
        q ∈ (surgeryNorthChart R e).source ∧
        ψ (surgeryNorthChart R e q, 0) =
          surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l q := by
  let height : UnitTwoSphere → ℝ := fun q => (heightCoordinates (q : E3)).2
  have hh : Continuous height :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hevent : ∀ᶠ q in 𝓝ˢ {q : UnitTwoSphere | height q = 0},
      q ∈ (surgeryNorthChart R e).source ∧
      ψ (surgeryNorthChart R e q, 0) =
        surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l q := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro q hq
    have hq0 : height q = 0 := hq
    have hqN : q ∈ northSphereDomain := by
      change -1 < height q
      rw [hq0]
      norm_num
    have hcoord : northSphereCoordinate q = (heightCoordinates (q : E3)).1 := by
      simp only [northSphereCoordinate, show (heightCoordinates (q : E3)).2 = 0 from hq0,
        add_zero, inv_one, one_smul]
    have hw1 : ‖northSphereCoordinate q‖ = 1 := by
      have hs := sphere_height_coordinates_sq q
      change ‖(heightCoordinates (q : E3)).1‖ ^ 2 + height q ^ 2 = 1 at hs
      rw [hq0] at hs
      rw [hcoord]
      nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
    have hwc : ContinuousAt northSphereCoordinate q :=
      northSphereCoordinate_contMDiffOn.continuousOn.continuousAt
        (northSphereDomain_isOpen.mem_nhds hqN)
    have hR0 := (eventually_nhdsSet_iff_forall.mp hRnear (northSphereCoordinate q)
      (mem_sphere_zero_iff_norm.mpr hw1)).self_of_nhds
    rw [hw1, surgeryMatchingRadius_one,
      NormedSpace.normalize_eq_self_of_norm_eq_one hw1] at hR0
    have hRn : ‖R (northSphereCoordinate q)‖ = r := by
      rw [hR0, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw1, mul_one]
    have hRcont : ContinuousAt (fun p => R (northSphereCoordinate p)) q :=
      R.contMDiff_toFun.continuous.continuousAt.comp hwc
    have hRband : ∀ᶠ p in 𝓝 q, |‖R (northSphereCoordinate p)‖ - 1| < delta :=
      (hRcont.norm.sub_const 1).abs.eventually_lt continuousAt_const (by
        change |‖R (northSphereCoordinate q)‖ - 1| < delta
        rw [hRn, abs_of_nonpos (sub_nonpos.mpr hr1.le)]
        linarith)
    have hradius : ContinuousAt
        (fun p => surgeryMatchingRadius r (l / k) ‖northSphereCoordinate p‖) q :=
      (surgeryMatchingRadius_contDiff r (l / k)).continuous.continuousAt.comp hwc.norm
    have hpositive : ∀ᶠ p in 𝓝 q,
        0 < surgeryMatchingRadius r (l / k) ‖northSphereCoordinate p‖ :=
      continuousAt_const.eventually_lt hradius (by rw [hw1, surgeryMatchingRadius_one]; exact hr)
    have hnonzero : ∀ᶠ p in 𝓝 q, northSphereCoordinate p ≠ 0 :=
      hwc.eventually_ne (by intro hz; simp [hz] at hw1)
    have hmatch : ∀ᶠ p in 𝓝 q,
        R (northSphereCoordinate p) =
          surgeryMatchingRadius r (l / k) ‖northSphereCoordinate p‖ •
            NormedSpace.normalize (northSphereCoordinate p) :=
      hwc.eventually (eventually_nhdsSet_iff_forall.mp hRnear _
        (mem_sphere_zero_iff_norm.mpr hw1))
    have hsmall : ∀ᶠ p in 𝓝 q, |height p| < 1 / 4 :=
      hh.continuousAt.abs.eventually_lt continuousAt_const (by rw [hq0]; norm_num)
    have hjoin : sigma * (k * (1 - r)) ∈ Ioo (-D.width) D.width := by
      apply abs_lt.mp
      rw [abs_mul, hsigma, one_mul, abs_of_pos (mul_pos hk (sub_pos.mpr hr1))]
      exact hcwidth
    have htcont : Continuous (fun p => sigma * (k * (1 - r) + l * height p)) :=
      continuous_const.mul (continuous_const.add (continuous_const.mul hh))
    have htime : ∀ᶠ p in 𝓝 q,
        sigma * (k * (1 - r) + l * height p) ∈ Ioo (-D.width) D.width :=
      htcont.continuousAt.eventually (isOpen_Ioo.mem_nhds (by simpa [hq0] using hjoin))
    filter_upwards [northSphereDomain_isOpen.mem_nhds hqN, hRband, hpositive,
      hnonzero, hmatch, hsmall, htime] with p hpN hpband hppos hpne hpmatch hpsmall hptime
    have hpe := hnear (R (northSphereCoordinate p)) hpband
    refine ⟨⟨hpN, hpe.1⟩, ?_⟩
    have hxne : (heightCoordinates (p : E3)).1 ≠ 0 := by
      intro hx
      apply hpne
      simp [northSphereCoordinate, hx]
    have hcancel : k * (l / k) = l := by field_simp [hk.ne']
    rw [surgeryNorthChart_collar_formula R e D.sourceCollar r (l / k) k sigma
      hpN hpne hppos hpmatch hpe.2, hcancel,
      northSphereCoordinate_circleDirection hpN hxne,
      D.reconstruction _ _ hptime, surgeryCapMap,
      surgeryCapCoordinates_cylinder a b ha hb ha0 hb0 hanear hbfar
        t sigma (k * (1 - r)) l p hpsmall.le]
  obtain ⟨U, hU, hzero, hformula⟩ := eventually_nhdsSet_iff_exists.mp hevent
  obtain ⟨eta, heta, hband⟩ := exists_uniform_zero_level_band height hh hU hzero
  exact ⟨eta, heta, fun q hq => hformula q (hband q hq)⟩

end PoincareConjecture.M25.Topology3D
