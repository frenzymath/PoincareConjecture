import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPrecompose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm Poincare.Analysis.Calculus

namespace PoincareConjecture

noncomputable def roundCylinderCoordinateTransition (p q : UnitTwoSphere) :
    RoundCylinderCoordinates → RoundCylinderCoordinates :=
  fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) p
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1), x.2)

theorem contDiffOn_roundCylinderCoordinateTransition (p q : UnitTwoSphere)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2) :
    ContDiffOn ℝ ∞ (roundCylinderCoordinateTransition p q)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) := by
  exact ((contDiffOn_sphere_chart_transition p q hpq).comp contDiffOn_fst
    (fun _ hx => hx.1)).prodMk contDiffOn_snd

theorem norm_roundCylinderCoordinateTransition_fst_le_two (p q : UnitTwoSphere)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {x : RoundCylinderCoordinates}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    ‖(roundCylinderCoordinateTransition p q x).1‖ ≤ 2 := by
  have hx' : ‖x.1‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  let z := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1
  have hdist : ‖(z : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (z : EuclideanSpace ℝ (Fin 3)) q p).trans
      (add_le_add (norm_sphere_chart_symm_sub_center_le q x.1) le_rfl)
    linarith
  have hinner : 0 ≤ ⟪(p : EuclideanSpace ℝ (Fin 3)), z⟫_ℝ := by
    have h := real_inner_le_norm (p : EuclideanSpace ℝ (Fin 3)) (p - z)
    rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p,
      norm_sub_rev] at h
    nlinarith
  exact norm_sphere_chart_le_two_of_nonneg_inner p z hinner

theorem exists_compact_roundCylinderCoordinateTransition_target
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    ∃ T : Set RoundCylinderCoordinates, IsCompact T ∧
      T ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3 ×ˢ univ ∧
      ∀ i, MapsTo (roundCylinderCoordinateTransition p (q i)) K T := by
  refine ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 ×ˢ (Prod.snd '' K),
    (isCompact_closedBall _ _).prod (hK.image continuous_snd), ?_, ?_⟩
  · intro x hx
    exact ⟨Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx.1).trans_lt (by norm_num)),
      mem_univ _⟩
  · intro i x hx
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_roundCylinderCoordinateTransition_fst_le_two p (q i) (hpq i) (hKU hx),
      by change x.2 ∈ Prod.snd '' K; exact mem_image_of_mem Prod.snd hx⟩

theorem exists_uniform_roundCylinderCoordinateTransition_jet_bound
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K)
    (hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ K →
      ‖iteratedFDeriv ℝ m (roundCylinderCoordinateTransition p (q i)) x‖ ≤ C := by
  obtain ⟨A, hA⟩ := exists_uniform_sphere_chart_transition_jet_bound p q hpq m
  let L := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    ((contDiff_snd : ContDiff ℝ ∞ (Prod.snd : RoundCylinderCoordinates → ℝ)).continuous_iteratedFDeriv
      (m := m) (by exact_mod_cast le_top)).continuousOn
  let C : ℝ := max (A * ∏ _ : Fin m, ‖L‖) (max D 0)
  have hC : 0 ≤ C := (le_max_right D 0).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro i x hx
  let f := (chartAt (EuclideanSpace ℝ (Fin 2)) p) ∘
    (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm
  have hfs : ContDiffAt ℝ ∞ f x.1 :=
    (contDiffOn_sphere_chart_transition p (q i) (hpq i)).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hKU hx).1)
  have hfl : ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ C := by
    rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L hfs m]
    exact ((iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le
      (fun _ : Fin m => L)).trans
      ((mul_le_mul_of_nonneg_right (hA i x.1 (hKU hx).1)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)).trans (le_max_left _ _))
  change ‖iteratedFDeriv ℝ m (fun y => ((f ∘ L) y, y.2)) x‖ ≤ C
  have hfls : ContDiffAt ℝ ∞ (f ∘ L) x := hfs.comp x L.contDiff.contDiffAt
  rw [iteratedFDeriv_prodMk hfls contDiffAt_snd (by exact_mod_cast le_top)]
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  apply max_le
  · exact ((iteratedFDeriv ℝ m (f ∘ L) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hfl (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  · exact ((iteratedFDeriv ℝ m (Prod.snd : RoundCylinderCoordinates → ℝ) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hD x hx).trans
        ((le_max_left D 0).trans (le_max_right _ _)))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem roundCylinderCoordinateTransition_chart_inverse (p q : UnitTwoSphere)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {x : RoundCylinderCoordinates}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
        (roundCylinderCoordinateTransition p q x).1,
      (roundCylinderCoordinateTransition p q x).2) =
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2) := by
  exact Prod.ext ((chartAt (EuclideanSpace ℝ (Fin 2)) p).left_inv
    (sphere_chart_transition_mapsTo_ball p q hpq x.1 hx.1).1) rfl

theorem roundCylinderCoordinateTransition_chart_inverse_eventuallyEq
    (p q : UnitTwoSphere)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {x : RoundCylinderCoordinates}
    (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ) :
    (fun y : RoundCylinderCoordinates =>
      ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
          (roundCylinderCoordinateTransition p q y).1,
        (roundCylinderCoordinateTransition p q y).2)) =ᶠ[𝓝 x]
      (fun y => ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)) := by
  filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds hx] with y hy
  exact roundCylinderCoordinateTransition_chart_inverse p q hpq hy

end PoincareConjecture
