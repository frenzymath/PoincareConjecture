import PoincareConjecture.Proofs.M25.Topology3D.Space3.TransverseSphereCollar
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem contMDiffOn_sphere_time_velocity
    (A : UnitTwoSphere × ℝ → E3) {V : Set UnitTwoSphere} (hV : IsOpen V)
    {eta : ℝ} (heta : 0 < eta)
    (hA : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ A
      (V ×ˢ Ioo (-eta) eta)) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun p => deriv (fun s : ℝ => A (p, s)) 0) V := by
  intro p hp
  have hAat := hA.contMDiffAt ((hV.prod isOpen_Ioo).mem_nhds
    (show (p, (0 : ℝ)) ∈ V ×ˢ Ioo (-eta) eta from
      ⟨hp, neg_lt_zero.mpr heta, heta⟩))
  have hd := ContMDiffAt.mfderiv_apply
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E3)) (J := 𝓡 2) (J' := 𝓡 2)
    (m := ∞) (n := ∞) (x₀ := p)
    (fun q : UnitTwoSphere => fun s : ℝ => A (q, s))
    (fun _ : UnitTwoSphere => (0 : ℝ))
    (fun q : UnitTwoSphere => q) (fun _ : UnitTwoSphere => (1 : ℝ))
    hAat contMDiffAt_const contMDiffAt_id contMDiffAt_const (by simp)
  have hvel : ContMDiffAt (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun q : UnitTwoSphere => deriv (fun s : ℝ => A (q, s)) 0) p := by
    simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv,
      fderiv_apply_one_eq_deriv] using hd
  exact hvel.contMDiffWithinAt

theorem exists_sphere_candidate_time_sign
    (j N : UnitTwoSphere → E3) (A : UnitTwoSphere × ℝ → E3)
    {V : Set UnitTwoSphere} (hV : IsOpen V) (hc : IsPreconnected V)
    {eta : ℝ} (heta : 0 < eta)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hN : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N)
    (hunit : ∀ p, ‖N p‖ = 1)
    (horth : ∀ p (v : TangentSpace (𝓡 2) p),
      ⟪N p, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0)
    (hA : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ A
      (V ×ˢ Ioo (-eta) eta))
    (hzero : ∀ p ∈ V, A (p, 0) = j p)
    (hfull : ∀ p ∈ V,
      Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) A (p, 0))) :
    ∃ eps : ℝ, |eps| = 1 ∧ ∀ p ∈ V,
      0 < ⟪N p, eps • deriv (fun s : ℝ => A (p, s)) 0⟫_ℝ := by
  let velocity : UnitTwoSphere → E3 := fun p => deriv (fun s : ℝ => A (p, s)) 0
  have hvel : ContMDiffOn (𝓡 2) 𝓘(ℝ, E3) ∞ velocity V :=
    contMDiffOn_sphere_time_velocity A hV heta hA
  have hne (p : UnitTwoSphere) (hp : p ∈ V) : ⟪N p, velocity p⟫_ℝ ≠ 0 := by
    have hAt : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) A (p, 0) :=
      (hA.contMDiffAt ((hV.prod isOpen_Ioo).mem_nhds
        ⟨hp, neg_lt_zero.mpr heta, heta⟩)).mdifferentiableAt (by simp)
    let L : (TangentSpace (𝓡 2) p × ℝ) →L[ℝ] E3 :=
      mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) A (p, 0)
    have hslice : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (fun q : UnitTwoSphere => (q, (0 : ℝ))) p :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hd := (hAt.hasMFDerivAt.comp p hslice.hasMFDerivAt).mfderiv
    rw [mfderiv_prod_left] at hd
    have heq : (fun q : UnitTwoSphere => A (q, 0)) =ᶠ[𝓝 p] j := by
      filter_upwards [hV.mem_nhds hp] with q hq
      exact hzero q hq
    have hjd : mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun q => A (q, 0)) p =
        mfderiv (𝓡 2) 𝓘(ℝ, E3) j p :=
      ((hj.mdifferentiable (by simp) p).hasMFDerivAt.congr_of_eventuallyEq heq).mfderiv
    have htangent (v : TangentSpace (𝓡 2) p) :
        L (v, 0) = mvfderiv (𝓡 2) j p v := by
      have hv := congrArg (fun F => F v) hd.symm
      change L (v, 0) = mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun q => A (q, 0)) p v at hv
      rwa [hjd] at hv
    have htime : L (0, 1) = velocity p := mfderiv_sphere_product_time A p hAt
    have hsplit (v : TangentSpace (𝓡 2) p) (s : ℝ) :
        L (v, s) = mvfderiv (𝓡 2) j p v + s • velocity p := by
      have he : (v, s) = (v, (0 : ℝ)) +
          s • ((0 : TangentSpace (𝓡 2) p), (1 : ℝ)) := by simp
      rw [he, map_add, map_smul, htangent, htime]
    intro hbad
    obtain ⟨u, hu⟩ := (show Function.Surjective L from (hfull p hp).2) (N p)
    have hself : ⟪N p, N p⟫_ℝ = 0 := by
      have horth' : ⟪N p, mvfderiv (𝓡 2) j p u.1⟫_ℝ = 0 := horth p u.1
      calc
        ⟪N p, N p⟫_ℝ = ⟪N p, L (u.1, u.2)⟫_ℝ :=
          congrArg (fun z : E3 => ⟪N p, z⟫_ℝ) hu.symm
        _ = 0 := by
          rw [hsplit, inner_add_right, real_inner_smul_right, horth', hbad]
          simp
    rw [real_inner_self_eq_norm_sq, hunit, one_pow] at hself
    exact one_ne_zero hself
  have hcont : ContinuousOn (fun p => ⟪N p, velocity p⟫_ℝ) V :=
    hN.continuous.continuousOn.inner hvel.continuousOn
  rcases hc.mapsTo_Ioi_or_Iio hcont hne with hpos | hneg
  · refine ⟨1, by norm_num, ?_⟩
    intro p hp
    simpa only [one_smul, Set.mem_Ioi, velocity] using hpos hp
  · refine ⟨-1, by norm_num, ?_⟩
    intro p hp
    simpa only [neg_one_smul, inner_neg_right] using neg_pos.mpr (hneg hp)

end PoincareConjecture.M25.Topology3D
