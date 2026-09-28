import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab
import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_middle_overlap_slab_height {L κ η : ℝ}
    (hL : 0 ≤ L) (hκ : κ ∈ Ioc 0 1) (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ (q : UnitTwoSphere)
        (s : ℝ), s ∈ Icc ((N.coordinate_inverse N'.center).2 - L)
          ((N.coordinate_inverse N'.center).2 + L) →
        |(N'.coordinate_inverse (N.coordinate_map (q, s))).2 -
          σ * (s - (N.coordinate_inverse N'.center).2)| < η := by
  let τ := min (1 / 4) (η / (16 * (Real.pi + L + 1)))
  have hden : 0 < 16 * (Real.pi + L + 1) := by positivity
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη hden)
  have hτquarter : τ ≤ 1 / 4 := min_le_left _ _
  have hbudget : 4 * τ * (Real.pi + L + 1) ≤ η / 4 := by
    have h := (le_div_iff₀ hden).mp
      (show τ ≤ η / (16 * (Real.pi + L + 1)) from min_le_right _ _)
    nlinarith
  obtain ⟨εb, hbpos, hbcap, hslab⟩ := exists_middle_overlap_slab.{u} hL hκ
  obtain ⟨εa, hapos, _, horient⟩ :=
    exists_intersecting_coherent_orientation.{u} (η := τ) ⟨hτ, by linarith⟩
  obtain ⟨εh, hhpos, _, hhorizontal⟩ :=
    exists_intersecting_transition_height_horizontal_bound.{u}
      (α := 4 * τ) (by positivity)
  obtain ⟨εs, hspos, _, hscale⟩ := exists_intersecting_scale_control.{u} hτ
  refine ⟨min εb (min εa (min εh εs)),
    lt_min hbpos (lt_min hapos (lt_min hhpos hspos)),
    (min_le_left _ _).trans hbcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter hmiddle
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let s0 := (N.coordinate_inverse N'.center).2
  let q0 := (N.coordinate_inverse N'.center).1
  let I := Icc (s0 - L) (s0 + L)
  let H : RoundCylinderSpace → ℝ := fun z => (N'.coordinate_inverse (N.coordinate_map z)).2
  have hsub : univ ×ˢ I ⊆ N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier :=
    hslab N N' (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _))
      hcenter hmiddle
  have hpre : IsPreconnected (univ ×ˢ I : Set RoundCylinderSpace) :=
    isPreconnected_univ.prod (convex_Icc _ _).isPreconnected
  obtain ⟨σ, hσ, haxis⟩ := horient N N'
    (hN.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hN'.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (univ ×ˢ I) hpre hsub
  have hratio : |N.scale / N'.scale - 1| < τ :=
    (hscale N' N
      (hN'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      (hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      ⟨N'.center, (N'.mem_central_sphere_iff _).mp N'.center_on_central_sphere |>.1,
        hcenter⟩).2
  have hr : N.scale / N'.scale ≤ 2 := by linarith [(abs_lt.mp hratio).2]
  have hanchor : H (q0, s0) = 0 := by
    change (N'.coordinate_inverse
      (N.coordinate_map (N.coordinate_inverse N'.center))).2 = 0
    rw [N.coordinate_map_coordinate_inverse hcenter]
    exact ((N'.mem_central_sphere_iff _).mp N'.center_on_central_sphere).2
  have hs0 : s0 ∈ I := ⟨by linarith, by linarith⟩
  have hdiff (s : ℝ) (hs : s ∈ I) : DifferentiableAt ℝ (fun r => H (q0, r)) s := by
    have hz := hsub (show (q0, s) ∈ univ ×ˢ I from ⟨mem_univ _, hs⟩)
    have hm := N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds hz.1)
    have hi := N'.coordinate_inverse_smooth.contMDiffAt (N'.carrier_open.mem_nhds hz.2)
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => (q0, r)) s := contMDiffAt_const.prodMk contMDiffAt_id
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((contMDiffAt_snd.comp s (hi.comp s (hm.comp s hp))).mdifferentiableAt (by simp))
  let G : ℝ → ℝ := fun s => H (q0, s) - σ * (s - s0)
  have hGdiff (s : ℝ) (hs : s ∈ I) : DifferentiableAt ℝ G s :=
    (hdiff s hs).sub ((differentiableAt_id.sub_const s0).const_mul σ)
  have hGderiv (s : ℝ) (hs : s ∈ I) :
      deriv G s = deriv (fun r => H (q0, r)) s - σ := by
    have hfun : ((fun r => H (q0, r)) - fun y => σ * (id y - s0)) = G := rfl
    simpa only [hfun, mul_one] using
      ((hdiff s hs).hasDerivAt.sub (((hasDerivAt_id s).sub_const s0).const_mul σ)).deriv
  have hGbound (s : ℝ) (hs : s ∈ I) : ‖deriv G s‖ ≤ 3 * τ := by
    rw [hGderiv s hs, Real.norm_eq_abs]
    have hz : (q0, s) ∈ univ ×ˢ I := ⟨mem_univ _, hs⟩
    exact N.transition_height_axial_error N' (hsub hz).1 (hsub hz).2 hσ hτ.le
      hratio.le hr (by simpa only [mul_assoc] using (haxis (q0, s) hz).le)
  have hG0 : G s0 = 0 := by simp only [G, hanchor, sub_self, mul_zero]
  refine ⟨σ, hσ, ?_⟩
  intro q s hs
  change s ∈ I at hs
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (hsub (show (q0, s) ∈ univ ×ˢ I from ⟨mem_univ _, hs⟩)).1.2
  have hslice : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : UnitTwoSphere => H (p, s)) :=
    N.contMDiff_transition_height_slice N' hsN
      (fun p => (hsub (show (p, s) ∈ univ ×ˢ I from ⟨mem_univ _, hs⟩)).2)
  have hosc : |H (q, s) - H (q0, s)| ≤ (4 * τ) * Real.pi := by
    apply sphere_height_oscillation_of_intrinsic_slope hslice (by positivity)
    intro p v
    have hz : (p, s) ∈ univ ×ˢ I := ⟨mem_univ _, hs⟩
    exact hhorizontal N N'
      (hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      (hN'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      (p, s) (hsub hz).1 (hsub hz).2 v
  have hlength : |s - s0| ≤ L := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hG : |G s| ≤ 3 * τ * L := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le hGdiff hGbound
      (convex_Icc (s0 - L) (s0 + L)) hs0 hs
    rw [hG0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left hlength (by positivity))
  change |H (q, s) - σ * (s - s0)| < η
  calc
    |H (q, s) - σ * (s - s0)| = |(H (q, s) - H (q0, s)) + G s| := by
      dsimp only [G]
      congr 1
      ring
    _ ≤ |H (q, s) - H (q0, s)| + |G s| := abs_add_le _ _
    _ ≤ (4 * τ) * Real.pi + 3 * τ * L := add_le_add hosc hG
    _ ≤ 4 * τ * (Real.pi + L + 1) := by nlinarith
    _ ≤ η / 4 := hbudget
    _ < η := by linarith

end PoincareConjecture.EpsilonNeck
