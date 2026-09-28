import PoincareConjecture.Proofs.M25.AppA_1_Necks.CenteredTransition
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CentralSphere
import PoincareConjecture.Proofs.M25.Mathlib.SphereChartJets
import PoincareConjecture.Proofs.M25.Mathlib.SecondDerivativeBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

open Poincare.Geometry.Riemannian.SpaceForm

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

noncomputable def transitionSphereChart (N N' : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  (N'.coordinate_inverse
    (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z, s))).1.val

theorem contDiff_transitionSphereChart (N N' : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsub : ∀ p : UnitTwoSphere, N.coordinate_map (p, s) ∈ N'.carrier) :
    ContDiff ℝ ∞ (N.transitionSphereChart N' q s) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
      (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) :=
    contMDiff_coe_sphere
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hc := sphere_chart_symm_contMDiff q z
  have hslice := (N.coordinate_slice_isSmoothEmbedding hs).contMDiff.contMDiffAt
    (x := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds (hsub _))).comp z (hslice.comp z hc)
  exact contMDiffAt_iff_contDiffAt.mp
    (hcoe.contMDiffAt.comp z (contMDiffAt_fst.comp z hi))

theorem exists_transitionSphereChart_hessian_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      (∀ p : UnitTwoSphere, N.coordinate_map (p, s) ∈ N'.carrier) →
      ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ 1 / 4 →
      ‖fderiv ℝ (fderiv ℝ (N.transitionSphereChart N' q s)) y‖ ≤ C := by
  obtain ⟨J, hJ, epsilon0, he0, hecap, hjet⟩ :=
    exists_intersecting_centeredEuclideanTransition_jet_bounds.{u}
  let i : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (RiemannianMetric.lineModelEquiv 2).toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
      (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap
  let a := max 1 ‖i‖
  let b := max 1 ‖P‖
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hiNorm : ‖i‖ ≤ a := le_max_right _ _
  have hPNorm : ‖P‖ ≤ b := le_max_right _ _
  refine ⟨(6 * a * b) ^ 2 + b * (J * a ^ 2 + 6 * a), by positivity,
    epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' q s hs hsub y hy
  let p := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y
  let z' := N'.coordinate_inverse (N.coordinate_map (p, s))
  have hs' : z'.2 ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ :=
    (N'.coordinate_inverse_mem _ (hsub p)).2
  have hx : N.coordinate_map (p, s) = N'.coordinate_map (z'.1, z'.2) :=
    (N'.coordinate_map_coordinate_inverse (hsub p)).symm
  let H := N.centeredEuclideanTransition N' p s z'.1 z'.2
  have hH0 : H 0 = 0 := N.centeredEuclideanTransition_zero N' p z'.1 hs' hx
  obtain ⟨W, hW, hW0, hH, hret⟩ := N.centeredEuclideanTransition_germ N' p z'.1 hs hs' hx
  change ContDiffOn ℝ ∞ H W at hH
  have hHjet := hjet N N' p z'.1 hN hN' hs hs' hx
  have hHfirst : ‖fderiv ℝ H 0‖ ≤ 6 := hHjet.1
  have hHsecond : ‖fderiv ℝ (fderiv ℝ H) 0‖ ≤ J :=
    hHjet.2.trans (by nlinarith [N.epsilon_lt_half, N'.epsilon_lt_half])
  let R := (chartAt (EuclideanSpace ℝ (Fin 2)) p) ∘
    (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
  obtain ⟨hR, _, hRinv, hRy, hRfirst, hRsecond⟩ := sphere_chart_recenter_twoJet q y hy
  change ContDiffOn ℝ ∞ R (Metric.ball 0 (1 / 2)) at hR
  change R y = 0 at hRy
  change ‖fderiv ℝ R y‖ ≤ 1 at hRfirst
  change ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ 3 * ‖y‖ at hRsecond
  have hRsecond' : ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ 1 := hRsecond.trans (by linarith)
  have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hy.trans_lt (by norm_num)
  let u := i ∘ R
  let U := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ∩ u ⁻¹' W
  have hu0 : u y = 0 := by simp [u, hRy]
  have hU : IsOpen U := (i.contDiff.comp_contDiffOn hR).continuousOn.isOpen_inter_preimage
    Metric.isOpen_ball hW
  have hyU : y ∈ U := ⟨hyball, by change u y ∈ W; rw [hu0]; exact hW0⟩
  have hRU : ContDiffOn ℝ ∞ R U := hR.mono inter_subset_left
  have hu : ContDiffOn ℝ ∞ u U := i.contDiff.comp_contDiffOn hRU
  have huW : MapsTo u U W := fun _ hz => hz.2
  let v := H ∘ u
  let w := P ∘ v
  have hv : ContDiffOn ℝ ∞ v U := hH.comp hu huW
  have hw : ContDiffOn ℝ ∞ w U := P.contDiff.comp_contDiffOn hv
  have hv0 : v y = 0 := by simp [v, hu0, hH0]
  have hw0 : w y = 0 := by simp [w, hv0]
  let sigma (r : UnitTwoSphere) : EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin 3) := fun z =>
    ((chartAt (EuclideanSpace ℝ (Fin 2)) r).symm z).val
  have hsigma (r : UnitTwoSphere) : ContDiff ℝ ∞ (sigma r) := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
        (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) :=
      contMDiff_coe_sphere
    exact contMDiff_iff_contDiff.mp (hcoe.comp (sphere_chart_symm_contMDiff r))
  have heq : N.transitionSphereChart N' q s =ᶠ[𝓝 y] sigma z'.1 ∘ w := by
    filter_upwards [hU.mem_nhds hyU] with z hz
    have hparam : N.euclideanParametrization p s (u z) =
        N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z, s) := by
      simp only [u, Function.comp_apply, i, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inl_apply,
        euclideanParametrization, ContinuousLinearEquiv.symm_apply_apply,
        centeredParametrization, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
      rw [hRinv z hz.1]
    have hsource := (hret (u z) hz.2).2.2.1
    have hwz : w z = chartAt (EuclideanSpace ℝ (Fin 2)) z'.1
        (N'.coordinate_inverse (N.euclideanParametrization p s (u z))).1 := by
      simp [w, v, H, centeredEuclideanTransition, P]
    change _ = sigma z'.1 (w z)
    rw [hwz]
    change _ = ((chartAt (EuclideanSpace ℝ (Fin 2)) z'.1).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) z'.1
        (N'.coordinate_inverse (N.euclideanParametrization p s (u z))).1)).val
    rw [(chartAt (EuclideanSpace ℝ (Fin 2)) z'.1).left_inv hsource, hparam]
    rfl
  have hRd : DifferentiableAt ℝ R y :=
    (hRU.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
  have hud : DifferentiableAt ℝ u y :=
    (hu.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
  have hvd : DifferentiableAt ℝ v y :=
    (hv.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
  have hHd : DifferentiableAt ℝ H (u y) :=
    (hH.contDiffAt (hW.mem_nhds (huW hyU))).differentiableAt (by simp)
  have hDi : fderiv ℝ (i : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) =
      fun _ => i := funext fun _ => i.fderiv
  have hDP : fderiv ℝ (P : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) =
      fun _ => P := funext fun _ => P.fderiv
  have hufirst : ‖fderiv ℝ u y‖ ≤ a := by
    rw [show u = i ∘ R from rfl, fderiv_comp y i.differentiableAt hRd, i.fderiv]
    exact (i.opNorm_comp_le _).trans
      ((mul_le_mul hiNorm hRfirst (norm_nonneg _) ha.le).trans_eq (mul_one _))
  have husecond : ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ a := by
    have h := norm_fderiv_fderiv_comp_le_of_contDiffOn (f := R) (g := i)
      hU isOpen_univ hyU (hRU.of_le (by norm_cast)) i.contDiff.contDiffOn
      (fun _ _ => mem_univ _)
    rw [hDi, fderiv_const_apply, norm_zero, zero_mul, zero_add] at h
    exact h.trans ((mul_le_mul hiNorm hRsecond' (norm_nonneg _) ha.le).trans_eq (mul_one _))
  have hvfirst : ‖fderiv ℝ v y‖ ≤ 6 * a := by
    rw [show v = H ∘ u from rfl, fderiv_comp y hHd hud]
    apply ((fderiv ℝ H (u y)).opNorm_comp_le _).trans
    rw [hu0]
    exact mul_le_mul hHfirst hufirst (norm_nonneg _) (by norm_num)
  have hvsecond : ‖fderiv ℝ (fderiv ℝ v) y‖ ≤ J * a ^ 2 + 6 * a := by
    have h := norm_fderiv_fderiv_comp_le_of_contDiffOn hU hW hyU
      (hu.of_le (by norm_cast)) (hH.of_le (by norm_cast)) huW
    rw [hu0] at h
    exact h.trans (by gcongr)
  have hwfirst : ‖fderiv ℝ w y‖ ≤ 6 * a * b := by
    rw [show w = P ∘ v from rfl, fderiv_comp y P.differentiableAt hvd, P.fderiv]
    apply (P.opNorm_comp_le _).trans
    exact (mul_le_mul hPNorm hvfirst (norm_nonneg _) hb.le).trans_eq (by ring)
  have hwsecond : ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ b * (J * a ^ 2 + 6 * a) := by
    have h := norm_fderiv_fderiv_comp_le_of_contDiffOn (f := v) (g := P)
      hU isOpen_univ hyU (hv.of_le (by norm_cast)) P.contDiff.contDiffOn
      (fun _ _ => mem_univ _)
    rw [hDP, fderiv_const_apply, norm_zero, zero_mul, zero_add] at h
    exact h.trans (mul_le_mul hPNorm hvsecond (norm_nonneg _) hb.le)
  have hsigmaD : ‖fderiv ℝ (sigma z'.1) 0‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (sphere_chart_symm_lipschitz z'.1)
  have hsigmaDD : ‖fderiv ℝ (fderiv ℝ (sigma z'.1)) 0‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
    intro v w
    rw [sphere_chart_symm_inclusion_fderiv_fderiv_zero]
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg, norm_eq_of_mem_sphere,
      mul_one, one_mul] using abs_real_inner_le_norm v w
  rw [heq.fderiv.fderiv_eq]
  have h := norm_fderiv_fderiv_comp_le_of_contDiffOn (f := w) (g := sigma z'.1)
    hU isOpen_univ hyU (hw.of_le (by norm_cast))
    ((hsigma z'.1).of_le (by norm_cast)).contDiffOn (fun _ _ => mem_univ _)
  rw [hw0] at h
  apply h.trans
  calc
    _ ≤ 1 * (6 * a * b) ^ 2 + 1 * (b * (J * a ^ 2 + 6 * a)) := by gcongr
    _ = _ := by ring

theorem exists_transitionSphereChart_error_hessian_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      (∀ p : UnitTwoSphere, N.coordinate_map (p, s) ∈ N'.carrier) →
      ∀ (A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (y : EuclideanSpace ℝ (Fin 2)), ‖y‖ ≤ 1 / 4 →
      ‖fderiv ℝ (fderiv ℝ (fun z => N.transitionSphereChart N' q s z -
        A (((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z).val))) y‖ ≤ C := by
  obtain ⟨C, hC, epsilon0, he0, hecap, hbound⟩ :=
    exists_transitionSphereChart_hessian_bound.{u}
  refine ⟨C + 2, by positivity, epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' q s hs hsub A y hy
  let F := N.transitionSphereChart N' q s
  let sigma : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := fun z =>
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z).val
  let G := A ∘ sigma
  have hF : ContDiff ℝ ∞ F := N.contDiff_transitionSphereChart N' q hs hsub
  have hsigma : ContDiff ℝ ∞ sigma := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
        (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) :=
      contMDiff_coe_sphere
    exact contMDiff_iff_contDiff.mp (hcoe.comp (sphere_chart_symm_contMDiff q))
  have hG : ContDiff ℝ ∞ G := A.toContinuousLinearMap.contDiff.comp hsigma
  have hDA : fderiv ℝ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) =
      fun _ => A.toContinuousLinearMap := funext fun _ => A.toContinuousLinearMap.fderiv
  have hAnorm : ‖A.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hGbound : ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ 2 := by
    have h := norm_fderiv_fderiv_comp_le_of_contDiffOn (f := sigma) (g := A)
      isOpen_univ isOpen_univ (mem_univ y)
      (hsigma.of_le (by norm_cast)).contDiffOn A.toContinuousLinearMap.contDiff.contDiffOn
      (fun _ _ => mem_univ _)
    rw [hDA, fderiv_const_apply, norm_zero, zero_mul, zero_add] at h
    exact h.trans ((mul_le_mul hAnorm
      (norm_fderiv_fderiv_sphere_chart_symm_inclusion_le q y hy)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have heq : fderiv ℝ (fun z => F z - G z) =
      fun z => fderiv ℝ F z - fderiv ℝ G z := by
    funext z
    exact fderiv_sub (hF.differentiable (by simp) z) (hG.differentiable (by simp) z)
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.contDiffAt.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have hDg : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.contDiffAt.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  change ‖fderiv ℝ (fderiv ℝ (fun z => F z - G z)) y‖ ≤ C + 2
  rw [heq]
  change ‖fderiv ℝ (fderiv ℝ F - fderiv ℝ G) y‖ ≤ C + 2
  rw [fderiv_sub hDf hDg]
  exact (norm_sub_le _ _).trans
    (add_le_add (hbound N N' hN hN' q hs hsub y hy) hGbound)

end PoincareConjecture.EpsilonNeck
