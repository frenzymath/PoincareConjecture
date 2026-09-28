import PoincareConjecture.Proofs.M35.CapGeometry.NeckInnerExit
import PoincareConjecture.Proofs.M35.CapGeometry.NeckBufferedBall










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.StandardCylinderPatch



theorem inner_slab_ball_subset_carrier {epsilon u ell L : ℝ}
    {x y : StandardCapSpace} (N : StandardCylinderPatch epsilon⁻¹ x)
    (g : RiemannianMetric 3 StandardCapSpace) (he : 0 < epsilon)
    (hesmall : epsilon ≤ 1 / 24) (hu : u ∈ Icc (-1) 0)
    (hL : L < ell) (hlong : ell < epsilon⁻¹)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (hy : y ∈ N.carrier) (hyax : |(N.inverse y).2| ≤ L) :
    g.ball y ((ell - L) / 2) ⊆ N.carrier := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro z hz
  by_contra hout
  obtain ⟨gamma, hzero, hone, hsmooth, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hz
  have hstart : gamma 0 ∈ N.coordinate '' (univ ×ˢ Ioo (-ell) ell) := by
    rw [hzero]
    exact ⟨N.inverse y, ⟨mem_univ _, abs_lt.mp (hyax.trans_lt hL)⟩,
      N.coordinate_right_inverse hy⟩
  obtain ⟨t, ht, hslab, hexit⟩ := N.exists_first_axial_exit_of_mem hlong
    gamma hsmooth.continuousOn hstart (hone ▸ hout)
  let clock : ℝ → ℝ := fun s => t * s
  let eta := gamma ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.mul contDiff_id
  have hclockmap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 t) := by
    intro s hs
    exact ⟨mul_nonneg ht.1.le hs.1,
      (mul_le_mul_of_nonneg_left hs.2 ht.1.le).trans_eq (mul_one t)⟩
  have hsmall : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have heta : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 eta (Icc 0 1) :=
    (hsmooth.mono hsmall).comp hclock.contMDiff.contMDiffOn hclockmap
  have himage : MapsTo eta (Icc (0 : ℝ) 1) N.carrier :=
    fun s hs => N.closed_axial_slab_subset_carrier hlong (hslab _ (hclockmap hs))
  have hmon : MonotoneOn clock (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab ht.1.le
  have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc (clock 0) (clock 1)) := by
    simpa only [clock, mul_zero, mul_one] using
      (hsmooth.mono hsmall).mdifferentiableOn one_ne_zero
  have hparam : g.pathELength eta 0 1 = g.pathELength gamma 0 t := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) zero_le_one
      hmon (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! h using 1
    simp only [clock, mul_zero, mul_one]
    rfl
  have hlenle : g.pathELength eta 0 1 ≤ g.pathELength gamma 0 1 :=
    hparam.le.trans (Manifold.pathELength_mono le_rfl ht.2)
  have hax := N.axial_edist_le_pathELength g he hesmall hu hclose eta heta himage
  have hax0 : eta 0 = y := by simpa only [eta, Function.comp_apply, clock, mul_zero] using hzero
  have hax1 : eta 1 = gamma t := by simp only [eta, Function.comp_apply, clock, mul_one]
  rw [hax0, hax1, edist_dist, Real.dist_eq] at hax
  have hdisplacement : ell - L ≤ |(N.inverse y).2 - (N.inverse (gamma t)).2| := by
    have h := abs_sub_abs_le_abs_sub (N.inverse (gamma t)).2 (N.inverse y).2
    rw [hexit, abs_sub_comm (N.inverse (gamma t)).2 (N.inverse y).2] at h
    linarith only [h, hyax]
  have hbound := (ENNReal.ofReal_le_ofReal hdisplacement).trans hax
  have hstrict : 2 * g.pathELength eta 0 1 < ENNReal.ofReal (ell - L) := by
    calc
      2 * g.pathELength eta 0 1 ≤ 2 * g.pathELength gamma 0 1 := mul_le_mul_right hlenle 2
      _ < 2 * ENNReal.ofReal ((ell - L) / 2) :=
        ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hlength
      _ = ENNReal.ofReal (2 * ((ell - L) / 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal (ell - L) := by congr 1; ring
  exact (not_lt_of_ge hbound) hstrict

end PoincareConjecture.StandardCylinderPatch
