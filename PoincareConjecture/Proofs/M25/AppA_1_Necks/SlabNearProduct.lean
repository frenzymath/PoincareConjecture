import PoincareConjecture.Proofs.M25.AppA_1_Necks.SphereSliceHessian
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SlabSphereControl
import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.Mathlib.SphereChartTangent
import PoincareConjecture.Proofs.M25.Mathlib.FiniteDifferenceInterpolation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

open Poincare.Geometry.Riemannian.SpaceForm




theorem exists_contained_slab_orthogonal_C1_control {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → ∀ s0 : ℝ,
      univ ×ˢ Icc (s0 - L) (s0 + L) ⊆
        N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier →
      ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Icc (s0 - L) (s0 + L) →
          ‖(N'.coordinate_inverse (N.coordinate_map (q, s))).1.val - A q.val‖ < η ∧
          (norm : (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) → ℝ)
            (mvfderiv (𝓡 2)
              (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).1.val) q -
              A.toContinuousLinearMap.comp (mvfderiv (𝓡 2)
                (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) q)) < η := by
  obtain ⟨C, hC, εH, hHpos, hHcap, hHess⟩ :=
    exists_transitionSphereChart_error_hessian_bound.{u}
  let h := min (1 / 4) (η / (4 * (C + 1)))
  let δ := η * h / 8
  have hh : 0 < h := lt_min (by norm_num) (div_pos hη (by positivity))
  have hδ : 0 < δ := by positivity
  have hhquarter : h ≤ 1 / 4 := min_le_left _ _
  have hbudget : C * h ≤ η / 4 := by
    have hm : h * (4 * (C + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  have hterm : 2 * δ / h = η / 4 := by
    dsimp only [δ]
    field_simp
    ring
  have hδsmall : δ < η := by
    dsimp only [δ]
    nlinarith
  obtain ⟨ε0, h0pos, _, hC0⟩ := exists_contained_slab_orthogonal_control.{u} hL hδ
  refine ⟨min εH ε0, lt_min hHpos h0pos, (min_le_left _ _).trans hHcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' s0 hsub
  obtain ⟨A, hA⟩ := hC0 N N' (hN.trans (min_le_right _ _))
    (hN'.trans (min_le_right _ _)) s0 hsub
  refine ⟨A, ?_⟩
  intro q s hs
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (hsub (show (q, s) ∈ univ ×ˢ Icc (s0 - L) (s0 + L) from ⟨mem_univ _, hs⟩)).1.2
  have hsN' (p : UnitTwoSphere) : N.coordinate_map (p, s) ∈ N'.carrier :=
    (hsub (show (p, s) ∈ univ ×ˢ Icc (s0 - L) (s0 + L) from ⟨mem_univ _, hs⟩)).2
  refine ⟨(hA q s hs).trans hδsmall, ?_⟩
  let F : UnitTwoSphere → EuclideanSpace ℝ (Fin 3) :=
    fun p => (N'.coordinate_inverse (N.coordinate_map (p, s))).1.val
  let B : UnitTwoSphere → EuclideanSpace ℝ (Fin 3) := fun p => A p.val
  let G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := fun z =>
    N.transitionSphereChart N' q s z - A (((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z).val)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
      (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hF : ContMDiff (𝓡 2) (𝓡 3) ∞ F := by
    intro p
    have hi := (N'.coordinate_inverse_smooth.contMDiffAt
      (N'.carrier_open.mem_nhds (hsN' p))).comp p
        (N.coordinate_slice_isSmoothEmbedding hsN).contMDiff.contMDiffAt
    exact hcoe.contMDiffAt.comp p (contMDiffAt_fst.comp p hi)
  have hB : ContMDiff (𝓡 2) (𝓡 3) ∞ B :=
    A.toContinuousLinearMap.contDiff.contMDiff.comp hcoe
  have hGfun : G = (F - B) ∘ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm := rfl
  have hG : ContDiff ℝ ∞ G := contMDiff_iff_contDiff.mp
    ((hF.sub hB).comp (sphere_chart_symm_contMDiff q))
  have hfirst : ‖fderiv ℝ G 0‖ < η := by
    have hb := norm_fderiv_zero_le_of_two_derivative_bounds hh hδ.le hC.le
      (fun z _ => hG.differentiable (by simp) z)
      (fun z _ => (hG.contDiffAt.fderiv_right (m := 1)
        (by norm_cast)).differentiableAt (by norm_num))
      (fun z _ => (hA ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z) s hs).le)
      (fun z hz => hHess N N' (hN.trans (min_le_left _ _))
        (hN'.trans (min_le_left _ _)) q hsN hsN' A z
        ((mem_closedBall_zero_iff.mp hz).trans hhquarter))
    rw [hterm] at hb
    exact hb.trans_lt (by linarith)
  have hDG : fderiv ℝ G 0 = mfderiv (𝓡 2) (𝓡 3) (F - B) q := by
    have hc := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3) 0
      ((hF.sub hB).mdifferentiable (by simp) _)
      ((sphere_chart_symm_contMDiff q).mdifferentiable (by simp) 0)
    rw [sphere_chart_symm_zero, sphere_chart_symm_mfderiv_zero] at hc
    change mfderiv (𝓡 2) (𝓡 3)
      ((F - B) ∘ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm) 0 =
        (mfderiv (𝓡 2) (𝓡 3) (F - B) q).comp (ContinuousLinearMap.id ℝ _) at hc
    simpa only [ContinuousLinearMap.comp_id, mfderiv_eq_fderiv, ← hGfun] using hc
  have hDB : mfderiv (𝓡 2) (𝓡 3) B q =
      A.toContinuousLinearMap.comp (mfderiv (𝓡 2) (𝓡 3)
        (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) q) := by
    have hc := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) q
      (mdifferentiableAt_iff_differentiableAt.mpr A.toContinuousLinearMap.differentiableAt)
      (hcoe.mdifferentiable (by simp) q)
    rw [mfderiv_eq_fderiv, A.toContinuousLinearMap.fderiv] at hc
    exact hc
  rw [hDG, mfderiv_sub (hF.mdifferentiable (by simp) q)
    (hB.mdifferentiable (by simp) q), hDB] at hfirst
  exact hfirst

set_option maxHeartbeats 1000000 in





theorem exists_middle_overlap_slab_near_product {L κ η : ℝ}
    (hL : 0 ≤ L) (hκ : κ ∈ Ioc 0 1) (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 → N'.center ∈ N.carrier →
      |(N.coordinate_inverse N'.center).2| ≤ (1 - κ) * N.epsilon⁻¹ →
      ∃ (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (σ : ℝ),
        (σ = 1 ∨ σ = -1) ∧
        let s0 := (N.coordinate_inverse N'.center).2
        let Ψ : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) × ℝ := fun z =>
          ((N'.coordinate_inverse (N.coordinate_map z)).1.val,
            (N'.coordinate_inverse (N.coordinate_map z)).2)
        let Pmodel : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) × ℝ := fun z =>
          (A z.1.val, σ * (z.2 - s0))
        univ ×ˢ Icc (s0 - (L + 1)) (s0 + (L + 1)) ⊆
          N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) ∞ Ψ
          (univ ×ˢ Ioo (s0 - (L + 1)) (s0 + (L + 1))) ∧
        ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Icc (s0 - L) (s0 + L) →
          ‖Ψ (q, s) - Pmodel (q, s)‖ < η ∧
          (norm : ((EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
            (EuclideanSpace ℝ (Fin 3) × ℝ)) → ℝ)
            (mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Ψ (q, s) -
              mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Pmodel (q, s)) < η := by
  let B := L + 1
  let α := η / 8
  let τ := min (1 / 4) (η / (32 * (Real.pi + B + 1)))
  have hB : 0 ≤ B := by dsimp only [B]; linarith
  have hα : 0 < α := by positivity
  have hden : 0 < 32 * (Real.pi + B + 1) := by positivity
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hη hden)
  have hτquarter : τ ≤ 1 / 4 := min_le_left _ _
  have hbudget : 4 * τ * (Real.pi + B + 1) ≤ η / 8 := by
    have h := (le_div_iff₀ hden).mp
      (show τ ≤ η / (32 * (Real.pi + B + 1)) from min_le_right _ _)
    nlinarith
  have hnormBudget : max (2 * α) (7 * τ) ≤ η / 4 := by
    apply max_le
    · dsimp only [α]; linarith
    · have h := mul_nonneg hτ.le (add_nonneg Real.pi_pos.le hB)
      nlinarith
  obtain ⟨εb, hbpos, hbcap, hslab⟩ := exists_middle_overlap_slab.{u} hB hκ
  obtain ⟨εf, hfpos, _, hframe⟩ := exists_contained_slab_orthogonal_C1_control.{u} hB hα
  obtain ⟨εv, hvpos, _, hvertical⟩ :=
    exists_intersecting_transition_sphere_axial_bound.{u} hα
  obtain ⟨εa, hapos, _, horient⟩ :=
    exists_intersecting_coherent_orientation.{u} (η := τ) ⟨hτ, by linarith⟩
  obtain ⟨εh, hhpos, _, hhorizontal⟩ :=
    exists_intersecting_transition_height_horizontal_bound.{u} (α := 4 * τ) (by positivity)
  obtain ⟨εs, hspos, _, hscale⟩ := exists_intersecting_scale_control.{u} hτ
  refine ⟨min εb (min εf (min εv (min εa (min εh εs)))),
    lt_min hbpos (lt_min hfpos (lt_min hvpos (lt_min hapos (lt_min hhpos hspos)))),
    (min_le_left _ _).trans hbcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter hmiddle
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hNs : N.epsilon ≤ εb ∧ N.epsilon ≤ εf ∧ N.epsilon ≤ εv ∧
      N.epsilon ≤ εa ∧ N.epsilon ≤ εh ∧ N.epsilon ≤ εs := by
    simpa only [le_min_iff] using hN
  have hN's : N'.epsilon ≤ εb ∧ N'.epsilon ≤ εf ∧ N'.epsilon ≤ εv ∧
      N'.epsilon ≤ εa ∧ N'.epsilon ≤ εh ∧ N'.epsilon ≤ εs := by
    simpa only [le_min_iff] using hN'
  rcases hNs with ⟨hNb, hNf, hNv, hNa, hNh, hNs⟩
  rcases hN's with ⟨hN'b, hN'f, hN'v, hN'a, hN'h, hN's⟩
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let s0 := (N.coordinate_inverse N'.center).2
  let q0 := (N.coordinate_inverse N'.center).1
  let I := Icc (s0 - B) (s0 + B)
  let F : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) :=
    fun z => (N'.coordinate_inverse (N.coordinate_map z)).1.val
  let H : RoundCylinderSpace → ℝ := fun z => (N'.coordinate_inverse (N.coordinate_map z)).2
  have hsub : univ ×ˢ I ⊆ N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier :=
    hslab N N' hNb hN'b hcenter hmiddle
  obtain ⟨A, hA⟩ := hframe N N' hNf hN'f s0 hsub
  have hpre : IsPreconnected (univ ×ˢ I : Set RoundCylinderSpace) :=
    isPreconnected_univ.prod (convex_Icc _ _).isPreconnected
  obtain ⟨σ, hσ, haxis⟩ := horient N N' hNa hN'a (univ ×ˢ I) hpre hsub
  let Ψ : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) × ℝ := fun z => (F z, H z)
  let Pmodel : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) × ℝ :=
    fun z => (A z.1.val, σ * (z.2 - s0))
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
      (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hFsm (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ I) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F z := by
    have hi := (N'.coordinate_inverse_smooth.contMDiffAt
      (N'.carrier_open.mem_nhds (hsub hz).2)).comp z
        (N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds (hsub hz).1))
    exact hcoe.contMDiffAt.comp z (contMDiffAt_fst.comp z hi)
  have hHsm (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ I) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H z := by
    have hi := (N'.coordinate_inverse_smooth.contMDiffAt
      (N'.carrier_open.mem_nhds (hsub hz).2)).comp z
        (N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds (hsub hz).1))
    exact contMDiffAt_snd.comp z hi
  have hΨsm (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ I) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) ∞ Ψ z :=
    (contMDiffAt_prod_module_iff Ψ).mpr ⟨hFsm z hz, hHsm z hz⟩
  have hPsm : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) ∞ Pmodel :=
    (contMDiff_prod_module_iff Pmodel).mpr
      ⟨(A.toContinuousLinearMap.contDiff.contMDiff.comp hcoe).comp contMDiff_fst,
        contMDiff_const.mul (contMDiff_snd.sub contMDiff_const)⟩
  have hratio : |N.scale / N'.scale - 1| < τ :=
    (hscale N' N hN's hNs
      ⟨N'.center, ((N'.mem_central_sphere_iff _).mp N'.center_on_central_sphere).1,
        hcenter⟩).2
  have hr : N.scale / N'.scale ≤ 2 := by linarith [(abs_lt.mp hratio).2]
  have hHD (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ I) :
      |deriv (fun r => H (q, r)) s - σ| ≤ 3 * τ := by
    have hz : (q, s) ∈ univ ×ˢ I := ⟨mem_univ _, hs⟩
    exact N.transition_height_axial_error N' (hsub hz).1 (hsub hz).2 hσ hτ.le
      hratio.le hr (by simpa only [mul_assoc] using (haxis (q, s) hz).le)
  have hanchor : H (q0, s0) = 0 := by
    change (N'.coordinate_inverse
      (N.coordinate_map (N.coordinate_inverse N'.center))).2 = 0
    rw [N.coordinate_map_coordinate_inverse hcenter]
    exact ((N'.mem_central_sphere_iff _).mp N'.center_on_central_sphere).2
  have hs0 : s0 ∈ I := ⟨by linarith, by linarith⟩
  have hdiff (s : ℝ) (hs : s ∈ I) : DifferentiableAt ℝ (fun r => H (q0, r)) s :=
    mdifferentiableAt_iff_differentiableAt.mp
      (((hHsm (q0, s) ⟨mem_univ _, hs⟩).comp s
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
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
    exact hHD q0 s hs
  have hG0 : G s0 = 0 := by simp only [G, hanchor, sub_self, mul_zero]
  have hheight (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ I) :
      |H (q, s) - σ * (s - s0)| ≤ η / 8 := by
    have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      (hsub (show (q0, s) ∈ univ ×ˢ I from ⟨mem_univ _, hs⟩)).1.2
    have hslice : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p : UnitTwoSphere => H (p, s)) :=
      N.contMDiff_transition_height_slice N' hsN
        (fun p => (hsub (show (p, s) ∈ univ ×ˢ I from ⟨mem_univ _, hs⟩)).2)
    have hosc : |H (q, s) - H (q0, s)| ≤ (4 * τ) * Real.pi := by
      apply sphere_height_oscillation_of_intrinsic_slope hslice (by positivity)
      intro p v
      have hz : (p, s) ∈ univ ×ˢ I := ⟨mem_univ _, hs⟩
      exact hhorizontal N N' hNh hN'h (p, s) (hsub hz).1 (hsub hz).2 v
    have hlength : |s - s0| ≤ B := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hGval : |G s| ≤ 3 * τ * B := by
      have hm := Convex.norm_image_sub_le_of_norm_deriv_le hGdiff hGbound
        (convex_Icc (s0 - B) (s0 + B)) hs0 hs
      rw [hG0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left hlength (by positivity))
    calc
      _ = |(H (q, s) - H (q0, s)) + G s| := by dsimp only [G]; congr 1; ring
      _ ≤ |H (q, s) - H (q0, s)| + |G s| := abs_add_le _ _
      _ ≤ (4 * τ) * Real.pi + 3 * τ * B := add_le_add hosc hGval
      _ ≤ 4 * τ * (Real.pi + B + 1) := by nlinarith
      _ ≤ η / 8 := hbudget
  refine ⟨A, σ, hσ, hsub, ?_, ?_⟩
  · intro z hz
    exact (hΨsm z ⟨hz.1, Ioo_subset_Icc_self hz.2⟩).contMDiffWithinAt
  · intro q s hs
    have hsI : s ∈ I := ⟨by dsimp only [I, B]; linarith [hs.1],
      by dsimp only [I, B]; linarith [hs.2]⟩
    have hz : (q, s) ∈ univ ×ˢ I := ⟨mem_univ _, hsI⟩
    change ‖Ψ (q, s) - Pmodel (q, s)‖ < η ∧
      (norm : ((EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 3) × ℝ)) → ℝ)
        (mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Ψ (q, s) -
          mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Pmodel (q, s)) < η
    refine ⟨?_, ?_⟩
    · change ‖(F (q, s) - A q.val, H (q, s) - σ * (s - s0))‖ < η
      rw [Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
      exact ⟨(hA q s hsI).1.trans (by dsimp only [α]; linarith),
        (hheight q s hsI).trans_lt (by linarith)⟩
    · have hΨd := (hΨsm (q, s) hz).mdifferentiableAt (by simp)
      have hPd := hPsm.mdifferentiable (by simp) (q, s)
      let D : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
          (EuclideanSpace ℝ (Fin 3) × ℝ) :=
        mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Ψ (q, s) -
          mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Pmodel (q, s)
      have hD : ‖D‖ ≤ max (2 * α) (7 * τ) := by
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        rintro ⟨v, t⟩
        let Dhor : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
          mvfderiv (𝓡 2) (fun p : UnitTwoSphere => F (p, s)) q -
            A.toContinuousLinearMap.comp (mvfderiv (𝓡 2)
              (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) q)
        have hFD : ‖Dhor‖ ≤ α := (hA q s hsI).2.le
        have hFV := (hvertical N N' hNv hN'v (q, s) (hsub hz).1 (hsub hz).2).le
        have hHH := hhorizontal N N' hNh hN'h (q, s) (hsub hz).1 (hsub hz).2 v
        rw [norm_mfderiv_sphere_inclusion] at hHH
        have hHV := hHD q s hsI
        have hFdiff := (hFsm (q, s) hz).mdifferentiableAt (by simp)
        have hHdiff := (hHsm (q, s) hz).mdifferentiableAt (by simp)
        have hformula : D (v, t) =
            (((mvfderiv (𝓡 2) (fun p : UnitTwoSphere => F (p, s)) q -
                A.toContinuousLinearMap.comp (mvfderiv (𝓡 2)
                  (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) q)) v) +
                t • deriv (fun r => F (q, r)) s,
              mvfderiv (𝓡 2) (fun p : UnitTwoSphere => H (p, s)) q v +
                t * (deriv (fun r => H (q, r)) s - σ)) := by
          have hpair (f : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3))
              (g : RoundCylinderSpace → ℝ)
              (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (q, s))
              (hg : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g (q, s)) :
              mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (f z, g z)) (q, s) =
                (mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) f (q, s)).prod
                  (mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) g (q, s)) := by
            apply ContinuousLinearMap.ext
            intro w
            have hp := mfderiv_prodMk (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
              (I' := 𝓡 3) (I'' := 𝓘(ℝ, ℝ)) hf hg
            rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
            exact congrArg (fun D => D w) hp
          have hsplit {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
              (f : RoundCylinderSpace → V)
              (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) f (q, s)) :
              mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) f (q, s) (v, t) =
                mvfderiv (𝓡 2) (fun p : UnitTwoSphere => f (p, s)) q v +
                  t • deriv (fun r => f (q, r)) s := by
            have h := mfderiv_prod_eq_add_apply
              (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, V))
              (p := (q, s)) (v := (v, t)) hf
            rw [mfderiv_eq_fderiv] at h
            calc
              _ = mvfderiv (𝓡 2) (fun p : UnitTwoSphere => f (p, s)) q v +
                  fderiv ℝ (fun r => f (q, r)) s t := h
              _ = _ := congrArg (fun z =>
                mvfderiv (𝓡 2) (fun p : UnitTwoSphere => f (p, s)) q v + z)
                  (fderiv_eq_smul_deriv t)
          let Q : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) := fun z => A z.1.val
          let K : RoundCylinderSpace → ℝ := fun z => σ * (z.2 - s0)
          have hQ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Q :=
            (A.toContinuousLinearMap.contDiff.contMDiff.comp hcoe).comp contMDiff_fst
          have hK : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ K :=
            contMDiff_const.mul (contMDiff_snd.sub contMDiff_const)
          have hQd := hQ.mdifferentiable (by simp) (q, s)
          have hKd := hK.mdifferentiable (by simp) (q, s)
          have hQh : mvfderiv (𝓡 2) (fun p : UnitTwoSphere => Q (p, s)) q =
              A.toContinuousLinearMap.comp (mvfderiv (𝓡 2)
                (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) q) := by
            have h := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) q
              (mdifferentiableAt_iff_differentiableAt.mpr A.toContinuousLinearMap.differentiableAt)
              (hcoe.mdifferentiable (by simp) q)
            rw [mfderiv_eq_fderiv, A.toContinuousLinearMap.fderiv] at h
            exact h
          have hKv : deriv (fun r => K (q, r)) s = σ := by
            change deriv (fun r => σ * (r - s0)) s = σ
            simpa only [id_eq, mul_one] using
              (((hasDerivAt_id s).sub_const s0).const_mul σ).deriv
          change ((mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (F z, H z)) (q, s)) -
            mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (Q z, K z)) (q, s)) (v, t) = _
          rw [hpair F H hFdiff hHdiff, hpair Q K hQd hKd]
          change (mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) F (q, s) (v, t) -
              mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Q (q, s) (v, t),
            mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) H (q, s) (v, t) -
              mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) K (q, s) (v, t)) = _
          rw [hsplit F hFdiff, hsplit Q hQd, hsplit H hHdiff, hsplit K hKd, hQh, hKv]
          have hQc : deriv (fun r => Q (q, r)) s = 0 := by
            change deriv (fun _ : ℝ => A q.val) s = 0
            exact deriv_const s _
          have hKh : mvfderiv (𝓡 2) (fun p : UnitTwoSphere => K (p, s)) q = 0 :=
            mvfderiv_const _
          rw [hQc, hKh]
          ext
          · simp only [smul_zero, add_zero, sub_apply]
            abel
          · simp only [zero_apply, zero_add, smul_eq_mul]
            ring
        rw [hformula, Prod.norm_def, Prod.norm_def, max_le_iff]
        have hvnorm : ‖v‖ ≤ max ‖v‖ ‖t‖ := le_max_left _ _
        have htnorm : ‖t‖ ≤ max ‖v‖ ‖t‖ := le_max_right _ _
        constructor
        · calc
            _ ≤ α * ‖v‖ + ‖t‖ * α := by
              apply (norm_add_le _ _).trans
              apply add_le_add
              · exact (Dhor.le_opNorm v).trans
                    (mul_le_mul_of_nonneg_right hFD (norm_nonneg _))
              · rw [norm_smul]
                exact mul_le_mul_of_nonneg_left hFV (norm_nonneg _)
            _ ≤ (2 * α) * max ‖v‖ ‖t‖ := by nlinarith
            _ ≤ max (2 * α) (7 * τ) * max ‖v‖ ‖t‖ := by gcongr; exact le_max_left _ _
        · rw [Real.norm_eq_abs]
          calc
            _ ≤ (4 * τ) * ‖v‖ + ‖t‖ * (3 * τ) := by
              apply (abs_add_le _ _).trans
              apply add_le_add hHH
              rw [abs_mul, ← Real.norm_eq_abs t]
              exact mul_le_mul_of_nonneg_left hHV (norm_nonneg _)
            _ ≤ (7 * τ) * max ‖v‖ ‖t‖ := by nlinarith
            _ ≤ max (2 * α) (7 * τ) * max ‖v‖ ‖t‖ := by gcongr; exact le_max_right _ _
      exact hD.trans_lt (hnormBudget.trans_lt (by linarith))

end PoincareConjecture.EpsilonNeck
