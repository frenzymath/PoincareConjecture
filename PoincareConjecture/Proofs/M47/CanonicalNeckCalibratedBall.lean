import PoincareConjecture.Proofs.M47.CanonicalNeckCalibratedAxial
import PoincareConjecture.Proofs.M35.Thm12_28.NeckBall

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.Proofs.M47

theorem standardNeck_ball_subset_of_axial_cutoff
    {epsilon u ell : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hell : 0 < ell) (hlong : ell < epsilon⁻¹)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate)) :
    g.ball x ((20 / 21 : ℝ) * ell) ⊆ N.carrier := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcenter : (N.inverse x).2 = 0 := by
    obtain ⟨q, hq⟩ := N.center_sphere
    have hdom : (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
      ⟨mem_univ _, ⟨neg_neg_of_pos N.length_pos, N.length_pos⟩⟩
    have hi := N.coordinate_left_inverse hdom
    rw [hq] at hi
    exact congrArg Prod.snd hi
  intro y hy
  by_contra hout
  obtain ⟨gamma, hzero, hone, hsmooth, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  obtain ⟨t, ht, hslab, hexit⟩ := N.exists_first_axial_exit hell hlong
    gamma hsmooth.continuousOn hzero (hone ▸ hout)
  let clock : ℝ → ℝ := fun s => t * s
  let eta := gamma ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.mul contDiff_id
  have hclockmap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 t) := by
    intro s hs
    exact ⟨mul_nonneg ht.1.le hs.1,
      (mul_le_mul_of_nonneg_left hs.2 ht.1.le).trans_eq (mul_one t)⟩
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have heta : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 eta (Icc 0 1) :=
    (hsmooth.mono hsub).comp hclock.contMDiff.contMDiffOn hclockmap
  have himage : MapsTo eta (Icc (0 : ℝ) 1) N.carrier :=
    fun s hs => N.closed_axial_slab_subset_carrier hlong (hslab _ (hclockmap hs))
  have hmon : MonotoneOn clock (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab ht.1.le
  have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc (clock 0) (clock 1)) := by
    simpa only [clock, mul_zero, mul_one] using
      (hsmooth.mono hsub).mdifferentiableOn one_ne_zero
  have hparam : g.pathELength eta 0 1 = g.pathELength gamma 0 t := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) zero_le_one
      hmon (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! h using 1
    simp only [clock, mul_zero, mul_one]
    rfl
  have hlenle : g.pathELength eta 0 1 ≤ g.pathELength gamma 0 1 :=
    hparam.le.trans (Manifold.pathELength_mono le_rfl ht.2)
  have hax := standardNeck_axial_edist_le_pathELength_calibrated
    N g he hsmall hu hclose eta heta himage
  have hax0 : eta 0 = x := by simpa only [eta, Function.comp_apply, clock, mul_zero] using hzero
  have hax1 : eta 1 = gamma t := by simp only [eta, Function.comp_apply, clock, mul_one]
  rw [hax0, hax1, hcenter, edist_dist, Real.dist_eq, zero_sub, abs_neg, hexit] at hax
  have hstrict : ENNReal.ofReal (21 / 20 : ℝ) * g.pathELength eta 0 1 <
      ENNReal.ofReal ell := by
    calc
      _ ≤ ENNReal.ofReal (21 / 20 : ℝ) * g.pathELength gamma 0 1 :=
        mul_le_mul_right hlenle _
      _ < ENNReal.ofReal (21 / 20 : ℝ) * ENNReal.ofReal ((20 / 21 : ℝ) * ell) :=
        ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal ((21 / 20 : ℝ) * ((20 / 21 : ℝ) * ell)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 21 / 20)]
      _ = ENNReal.ofReal ell := by congr 1; ring
  exact (not_lt_of_ge hax) hstrict

theorem standardNeck_center_ball_subset_calibrated
    {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate)) :
    g.ball x ((19 / 20 : ℝ) * epsilon⁻¹) ⊆ N.carrier := by
  have hell : 0 < (399 / 400 : ℝ) * epsilon⁻¹ := by positivity
  have hlong : (399 / 400 : ℝ) * epsilon⁻¹ < epsilon⁻¹ := by
    nlinarith [inv_pos.mpr he]
  have h := standardNeck_ball_subset_of_axial_cutoff N g he hsmall hu hell hlong hclose
  convert h using 1
  congr 1
  ring

theorem standardNeck_central_ball_subset_calibrated
    {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hsmall : epsilon ≤ 1 / 1200) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (q : UnitTwoSphere) :
    g.ball (N.coordinate (q, 0)) ((19 / 20 : ℝ) * epsilon⁻¹) ⊆ N.carrier := by
  let N' : StandardCylinderPatch epsilon⁻¹ (N.coordinate (q, 0)) :=
    { N with center_sphere := ⟨q, rfl⟩ }
  exact standardNeck_center_ball_subset_calibrated N' g he hsmall hu hclose

end PoincareConjecture.Proofs.M47
