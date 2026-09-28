import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthSpeed
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

variable {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
  {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
  (N : StandardEvolvingNeck atlas G v gamma z
    (Icc (-v * (G.connection v).scalarCurvature z) 0))
  (hsmall : gamma ≤ 1 / 1200)
  (hdisjoint : Disjoint N.patch.carrier
    {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
  (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)

include hsmall hdisjoint hshort

theorem standard_initial_neck_ball_subset_sharp
    {x : StandardCapSpace} (hx : x ∈ N.patch.carrier)
    (hheight : |(N.patch.inverse x).2| ≤ 1) :
    g0.metric.ball x ((20 / 29 : ℝ) * (gamma⁻¹ - 2)) ⊆ N.patch.carrier := by
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  let r := (20 / 29 : ℝ) * (gamma⁻¹ - 2)
  have hr : 0 < r := by dsimp only [r]; linarith
  let a := gamma⁻¹ - 1
  have ha : a < gamma⁻¹ := by dsimp only [a]; linarith
  let U := N.patch.coordinate '' (univ ×ˢ Ioo (-a) a)
  let K := N.patch.coordinate '' (univ ×ˢ Icc (-a) a)
  have hU : IsOpen U := N.patch.open_axial_slab ha.le
  have hK : IsClosed K := (N.patch.compact_axial_slab ha).isClosed
  have hUK : U ⊆ K := image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hcapture : closure U ⊆ K := closure_minimal hUK hK
  have hKC : K ⊆ N.patch.carrier := N.patch.closed_axial_slab_subset_carrier ha
  have hxU : x ∈ U := by
    refine ⟨N.patch.inverse x, ⟨mem_univ _, ?_⟩, N.patch.coordinate_right_inverse hx⟩
    apply abs_lt.mp
    dsimp only [a]
    linarith only [hheight, hL]
  intro y hy
  by_contra hyout
  have hyU : y ∉ U := fun h => hyout (hKC (hUK h))
  obtain ⟨p, hp0, hp1, hp, hlength, _⟩ := g0.metric.exists_short_path_in_ball x y hy
  obtain ⟨t, ht, hfrontier, _, hbefore⟩ := hp.continuousOn.exists_first_frontier_time
    zero_le_one hU (hp0.symm ▸ hxU) (hp1.symm ▸ hyU)
  have hendK : p t ∈ K := hcapture (frontier_subset_closure hfrontier)
  have hendout : p t ∉ U := by
    simpa only [hU.interior_eq] using hfrontier.2
  have hexit : |(N.patch.inverse (p t)).2| = a :=
    N.patch.axial_abs_eq_at_slab_exit ha hendK hendout
  have hprefix : MapsTo p (Icc 0 t) N.patch.carrier :=
    fun s hs => hKC (hcapture (hbefore hs))
  let clock : ℝ → ℝ := fun s => t * s
  let path := p ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.mul contDiff_id
  have hclockmap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 t) := by
    intro s hs
    exact ⟨mul_nonneg ht.1.le hs.1,
      (mul_le_mul_of_nonneg_left hs.2 ht.1.le).trans_eq (mul_one t)⟩
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc 0 1) :=
    (hp.mono hsub).comp hclock.contMDiff.contMDiffOn hclockmap
  have himage : MapsTo path (Icc (0 : ℝ) 1) N.patch.carrier :=
    fun s hs => hprefix (hclockmap hs)
  have hmon : MonotoneOn clock (Icc (0 : ℝ) 1) := by
    intro r _ s _ hrs
    exact mul_le_mul_of_nonneg_left hrs ht.1.le
  have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) p (Icc (clock 0) (clock 1)) := by
    simpa only [clock, mul_zero, mul_one] using
      (hp.mono hsub).mdifferentiableOn one_ne_zero
  have hparam : g0.metric.pathELength path 0 1 = g0.metric.pathELength p 0 t := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g0.metric.toRiemannianMetric⟩
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) zero_le_one
      hmon (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! h using 1
    simp only [clock, mul_zero, mul_one]
    rfl
  have hlenle : g0.metric.pathELength path 0 1 ≤ g0.metric.pathELength p 0 1 :=
    hparam.le.trans (M36.metric_pathELength_mono _ _ le_rfl ht.2)
  have haxis := standard_initial_neck_axial_path_length_sharp
    N hsmall hdisjoint hshort path hpath himage
  have hpath0 : path 0 = x := by
    simpa only [path, Function.comp_apply, clock, mul_zero] using hp0
  have hpath1 : path 1 = p t := by simp only [path, Function.comp_apply, clock, mul_one]
  rw [hpath0, hpath1, edist_dist, Real.dist_eq] at haxis
  have htriangle : |(N.patch.inverse (p t)).2| ≤
      |(N.patch.inverse x).2 - (N.patch.inverse (p t)).2| + |(N.patch.inverse x).2| := by
    calc
      _ = |((N.patch.inverse (p t)).2 - (N.patch.inverse x).2) +
          (N.patch.inverse x).2| := by congr 1; ring
      _ ≤ |(N.patch.inverse (p t)).2 - (N.patch.inverse x).2| +
          |(N.patch.inverse x).2| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (N.patch.inverse (p t)).2 (N.patch.inverse x).2]
  have hdisplacement : gamma⁻¹ - 2 ≤
      |(N.patch.inverse x).2 - (N.patch.inverse (p t)).2| := by
    rw [hexit] at htriangle
    dsimp only [a] at htriangle
    linarith only [htriangle, hheight]
  have hstrict : ENNReal.ofReal (29 / 20 : ℝ) * g0.metric.pathELength path 0 1 <
      ENNReal.ofReal |(N.patch.inverse x).2 - (N.patch.inverse (p t)).2| := by
    calc
      _ ≤ ENNReal.ofReal (29 / 20 : ℝ) * g0.metric.pathELength p 0 1 :=
        mul_le_mul_right hlenle _
      _ < ENNReal.ofReal (29 / 20 : ℝ) * ENNReal.ofReal r :=
        ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal (gamma⁻¹ - 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 29 / 20)]
        congr 1
        dsimp only [r]
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal hdisplacement
  exact not_lt_of_ge haxis hstrict

theorem standard_initial_neck_tip_distance_sharp
    {x : StandardCapSpace} (hx : x ∈ N.patch.carrier)
    (hheight : |(N.patch.inverse x).2| ≤ 1) :
    ENNReal.ofReal (g0.cylindrical_end.radius + 4 + (20 / 29 : ℝ) * (gamma⁻¹ - 2)) ≤
      g0.metric.edist 0 x := by
  have hL : (1200 : ℝ) ≤ gamma⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  exact standard_tip_distance_lower_of_ball_disjoint g0.metric
    (by linarith : 0 < (20 / 29 : ℝ) * (gamma⁻¹ - 2))
    (by linarith [g0.cylindrical_end.radius_pos] : 0 < g0.cylindrical_end.radius + 4)
    (standard_initial_neck_ball_subset_sharp N hsmall hdisjoint hshort hx hheight) hdisjoint

end PoincareConjecture.M47
