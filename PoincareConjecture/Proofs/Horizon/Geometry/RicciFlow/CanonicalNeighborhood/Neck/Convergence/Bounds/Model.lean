import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

private theorem mfderiv_comp_cylinder_chart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (q : UnitTwoSphere) (f : RoundCylinderSpace → M)
    (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2))
    (v : RoundCylinderCoordinates) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (fun y => f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)) p v =
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1 v.1, v.2) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm p.1 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  let L₁ := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  let L₂ := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  have h₁ := hc.comp p L₁.mdifferentiableAt
  have h₂ := L₂.mdifferentiableAt (x := p)
  have hh := mfderiv_comp p hf (h₁.prodMk h₂)
  have hL₁ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = L₁ :=
    L₁.mfderiv_eq
  have hL₂ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) L₂ p = L₂ :=
    L₂.mfderiv_eq
  rw [mfderiv_prodMk h₁ h₂, mfderiv_comp p hc L₁.mdifferentiableAt, hL₁, hL₂] at hh
  exact congrArg (fun L => L v) hh

noncomputable def roundCylinderModelCoefficients (p : RoundCylinderCoordinates) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
by
  let B : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
    ContinuousLinearMap.bilinearComp (σ₁₃' := RingHom.id ℝ)
      (innerSL ℝ : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  exact (2 * (16 / (‖p.1‖ ^ 2 + 4) ^ 2)) • B +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)

@[simp] theorem roundCylinderModelCoefficients_apply
    (p v w : RoundCylinderCoordinates) :
    roundCylinderModelCoefficients p v w =
      2 * (16 / (‖p.1‖ ^ 2 + 4) ^ 2) * ⟪v.1, w.1⟫_ℝ + v.2 * w.2 := rfl

theorem parametrizedCoefficients_cylinder_of_normalized_pullback
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {Φ : RoundCylinderSpace → M}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (s : ℝ)
    (hround : (fun z v w => s * roundCylinderPullback g Φ z v w) =
      EvolvingRoundCylinderMetric 0) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    s • g.parametrizedCoefficients
      (fun x => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x.1, x.2)) p =
      roundCylinderModelCoefficients p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have h := congrArg (fun B : RoundCylinderTwoTensor =>
    B (c.symm p.1, p.2)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1, w.2)) hround
  change s * g.inner (Φ (c.symm p.1, p.2))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (c.symm p.1, p.2)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (c.symm p.1, p.2)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1, w.2)) =
    2 * (1 - 0) * (roundSphereMetric 2).inner (c.symm p.1)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1) + v.2 * w.2 at h
  rw [roundSphereMetric_chart_symm_inner] at h
  simp only [smul_apply, smul_eq_mul,
    RiemannianMetric.parametrizedCoefficients_apply, roundCylinderModelCoefficients_apply]
  rw [mfderiv_comp_cylinder_chart q Φ p ((hΦ _).mdifferentiableAt (by simp)),
    mfderiv_comp_cylinder_chart q Φ p ((hΦ _).mdifferentiableAt (by simp))]
  convert h using 1
  ring

theorem contDiff_roundCylinderModelCoefficients :
    ContDiff ℝ ∞ roundCylinderModelCoefficients := by
  let : IsBoundedSMul ℝ
      (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)
  have hs : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      2 * (16 / (‖p.1‖ ^ 2 + 4) ^ 2)) :=
    contDiff_const.mul (contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 2)
      (fun p => by positivity))
  exact (hs.smul contDiff_const).add contDiff_const

theorem exists_roundCylinderModelCoefficients_jet_bound
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (m : ℕ) :
    ∃ Z : ℝ, 0 ≤ Z ∧ ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m roundCylinderModelCoefficients x‖ ≤ Z := by
  have hcont := ContDiff.continuous_iteratedFDeriv (m := m)
    (by norm_cast; exact le_top : (m : ℕ∞ω) ≤ ∞) contDiff_roundCylinderModelCoefficients
  obtain ⟨Z, hZ⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max 0 Z, le_max_left _ _, fun x hx => (hZ x hx).trans (le_max_right _ _)⟩

theorem roundCylinderModelCoefficients_center_quadratic_bounds
    (r : ℝ) (v : RoundCylinderCoordinates) :
    ‖v‖ ^ 2 ≤ roundCylinderModelCoefficients (0, r) v v ∧
      roundCylinderModelCoefficients (0, r) v v ≤ 3 * ‖v‖ ^ 2 := by
  simp only [roundCylinderModelCoefficients_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
    real_inner_self_eq_norm_sq]
  norm_num
  constructor
  · rw [Prod.norm_def]
    rcases le_total ‖v.1‖ ‖v.2‖ with h | h
    · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg ‖v.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg v.2, sq_nonneg ‖v.1‖]
  · have h₁ := norm_fst_le v
    have h₂ := norm_snd_le v
    have h₂sq : v.2 ^ 2 ≤ ‖v‖ ^ 2 := by
      have := sq_le_sq₀ (norm_nonneg v.2) (norm_nonneg v) |>.mpr h₂
      simpa only [Real.norm_eq_abs, sq_abs] using this
    nlinarith [sq_le_sq₀ (norm_nonneg v.1) (norm_nonneg v) |>.mpr h₁]

end PoincareConjecture
