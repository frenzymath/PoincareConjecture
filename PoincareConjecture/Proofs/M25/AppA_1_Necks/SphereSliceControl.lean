import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionMetric
import PoincareConjecture.Proofs.M25.Mathlib.RoundSphereDistortion
import PoincareConjecture.Proofs.M25.Mathlib.SphereFrameStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

open Poincare.Geometry.Riemannian.SpaceForm

theorem exists_contained_slice_diffeomorph_norm_bounds {K : ℝ} (hK : 1 < K) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
      (∀ q : UnitTwoSphere, N.coordinate_map (q, s) ∈ N'.carrier) →
      ∃ e : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        (∀ q, e q = (N'.coordinate_inverse (N.coordinate_map (q, s))).1) ∧
        (∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
          let V := (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v)
          let W := (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (e q)
              (mfderiv (𝓡 2) (𝓡 2) e q v))
          K⁻¹ * V ≤ W ∧ W ≤ K * V) ∧
        (∀ (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q),
          (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
              (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (e.symm q)
                (mfderiv (𝓡 2) (𝓡 2) e.symm q v)) ≤
            K * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
              (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) q v)) := by
  obtain ⟨εd, hdpos, hdcap, hbound⟩ :=
    exists_intersecting_transition_sphere_norm_bounds.{u} hK
  obtain ⟨εt, htpos, _, htrans⟩ := exists_intersecting_axial_transversality.{u}
  refine ⟨min εd εt, lt_min hdpos htpos, (min_le_left _ _).trans hdcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' s hs hsub
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (n := 2) (by norm_num)
  let F : UnitTwoSphere → UnitTwoSphere :=
    fun q => (N'.coordinate_inverse (N.coordinate_map (q, s))).1
  have hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ F :=
    N'.slice_projection_isLocalDiffeomorph_of_transverse N hs hsub
      (fun q => (htrans N N' (hN.trans (min_le_right _ _))
        (hN'.trans (min_le_right _ _)) (N.coordinate_map (q, s))
        (N.coordinate_map_mem ⟨mem_univ q, hs⟩) (hsub q)).2)
  let e := Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph
    (n := 0) F hlocal
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro q v
    exact hbound N N' (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _))
      (q, s) ⟨mem_univ q, hs⟩ (hsub q) v
  · intro q v
    have hlow := (hbound N N' (hN.trans (min_le_left _ _))
      (hN'.trans (min_le_left _ _)) (e.symm q, s) ⟨mem_univ _, hs⟩
      (hsub (e.symm q)) (mfderiv (𝓡 2) (𝓡 2) e.symm q v)).1
    have hde : mfderiv (𝓡 2) (𝓡 2) e (e.symm q)
        (mfderiv (𝓡 2) (𝓡 2) e.symm q v) = v := by
      have hc := mfderiv_comp_apply q (e.mdifferentiable (by simp) (e.symm q))
        (e.symm.mdifferentiable (by simp) q) v
      have heid : (e : UnitTwoSphere → UnitTwoSphere) ∘ e.symm = id :=
        funext e.apply_symm_apply
      rw [heid, mfderiv_id] at hc
      exact hc.symm
    change K⁻¹ * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (e.symm q)
          (mfderiv (𝓡 2) (𝓡 2) e.symm q v)) ≤
      (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (e (e.symm q))
          (mfderiv (𝓡 2) (𝓡 2) e (e.symm q)
            (mfderiv (𝓡 2) (𝓡 2) e.symm q v))) at hlow
    rw [hde, e.apply_symm_apply] at hlow
    have hmul := mul_le_mul_of_nonneg_left hlow (zero_lt_one.trans hK).le
    simpa only [← mul_assoc, mul_inv_cancel₀ (zero_lt_one.trans hK).ne', one_mul] using hmul

theorem exists_contained_slice_inner_control {η : ℝ} (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
      (∀ q : UnitTwoSphere, N.coordinate_map (q, s) ∈ N'.carrier) →
      ∀ p q : UnitTwoSphere,
        |inner ℝ (N'.coordinate_inverse (N.coordinate_map (p, s))).1.1
            (N'.coordinate_inverse (N.coordinate_map (q, s))).1.1 -
          inner ℝ p.1 q.1| < η := by
  let K := 1 + η / (2 * (Real.pi + 1))
  have hK : 1 < K := by
    have h : 0 < η / (2 * (Real.pi + 1)) := by positivity
    dsimp only [K]
    linarith
  obtain ⟨ε0, hpos, hcap, hcontrol⟩ := exists_contained_slice_diffeomorph_norm_bounds.{u} hK
  refine ⟨ε0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' s hs hsub p q
  obtain ⟨e, he, hf, hi⟩ := hcontrol N N' hN hN' s hs hsub
  have hb := sphere_inner_distortion_of_diffeomorph_tangent_bounds
    (by norm_num : 1 ≤ 2) e hK.le (fun x v => (hf x v).2) hi p q
  rw [he, he] at hb
  apply hb.trans_lt
  have hden : 0 < 2 * (Real.pi + 1) := by positivity
  change (1 + η / (2 * (Real.pi + 1)) - 1) * Real.pi < η
  rw [add_sub_cancel_left, div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).mpr
  nlinarith [Real.pi_pos]

theorem exists_contained_slice_orthogonal_control {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
      (∀ q : UnitTwoSphere, N.coordinate_map (q, s) ∈ N'.carrier) →
      ∃ A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        ∀ q : UnitTwoSphere,
          ‖(N'.coordinate_inverse (N.coordinate_map (q, s))).1.1 - A q.1‖ < ζ := by
  obtain ⟨η, hη, _, hframe⟩ :=
    EuclideanSpace.exists_linearIsometryEquiv_of_sphere_inner_close hζ
  obtain ⟨ε0, hpos, hcap, hcontrol⟩ := exists_contained_slice_inner_control.{u} hη
  refine ⟨ε0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' s hs hsub
  exact hframe (fun q => (N'.coordinate_inverse (N.coordinate_map (q, s))).1)
    (fun p q => (hcontrol N N' hN hN' s hs hsub p q).le)

end PoincareConjecture.EpsilonNeck
