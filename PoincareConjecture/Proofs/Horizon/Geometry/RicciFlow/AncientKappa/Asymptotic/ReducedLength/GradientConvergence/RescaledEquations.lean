import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.WeakEquations.ConjugateHeat
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Scaling
import Mathlib.Analysis.Calculus.Deriv.CompMul



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u
namespace PoincareConjecture.AncientRescaling

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {s : ℝ} (R : AncientRescaling K s)

theorem ae_reducedLength_hamiltonJacobi_coordinates
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    let g := R.flow.metric (-τ)
    let l := fun x => reducedLength K.flow 0 p (e x) (s * τ)
    ∀ᵐ x, x ∈ e.source →
      2 * deriv (fun a => reducedLength K.flow 0 p (e x) (s * a)) τ +
        fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) -
        (R.flow.connection (-τ)).scalarCurvature (e x) + l x / τ = 0 := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  filter_upwards [P.ae_reducedLength_hamiltonJacobi_coordinates p (mul_pos R.tau_pos hτ)
    e he hei] with x hx hxsrc
  have hh := hx hxsrc
  have hscalar := R.scalar_scale (-τ) (neg_neg_of_pos hτ) (e x)
  rw [show s * -τ = 0 - s * τ by ring] at hscalar
  rw [hscalar, R.inverse_pullbackCoefficients_scale hτ (hD.mfderiv_injective hxsrc),
    deriv_comp_mul_left]
  simp only [map_smul, smul_eq_mul]
  field_simp [R.tau_pos.ne', hτ.ne'] at hh ⊢
  nlinarith [hh]

theorem reducedLength_second_weak_coordinate_gradient_inequality
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O) (hOs : O ⊆ e.source)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) :
    let g := R.flow.metric (-τ)
    let l := fun x => reducedLength K.flow 0 p (e x) (s * τ)
    let B := fun x => (φ x *
      (-fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
        (R.flow.connection (-τ)).scalarCurvature (e x) + (l x - (n : ℝ)) / τ) -
      2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) *
      g.pullbackVolumeDensity e x
    IntegrableOn B O ∧ (∫ x in O, B x) ≤ 0 := by
  let g := R.flow.metric (-τ)
  let l := fun x => reducedLength K.flow 0 p (e x) (s * τ)
  let B := fun x => (φ x *
    (-fderiv ℝ l x (((K.flow.metric (0 - s * τ)).pullbackCoefficients e x).inverse
        (fderiv ℝ l x)) +
      (K.flow.connection (0 - s * τ)).scalarCurvature (e x) +
        (l x - (n : ℝ)) / (s * τ)) -
    2 * fderiv ℝ φ x (((K.flow.metric (0 - s * τ)).pullbackCoefficients e x).inverse
      (fderiv ℝ l x))) * (K.flow.metric (0 - s * τ)).pullbackVolumeDensity e x
  let c := Real.sqrt ((1 / s) ^ n) * s
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) R.tau_pos.le
  obtain ⟨hi, hw⟩ := P.reducedLength_second_weak_coordinate_gradient_inequality
    p (mul_pos R.tau_pos hτ) e he hei hO hOs hφ hφc hφO hφ0
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have heq : (fun x => c * B x) =ᵐ[volume.restrict O]
      (fun x => (φ x *
        (-fderiv ℝ l x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x)) +
          (R.flow.connection (-τ)).scalarCurvature (e x) + (l x - (n : ℝ)) / τ) -
        2 * fderiv ℝ φ x ((g.pullbackCoefficients e x).inverse (fderiv ℝ l x))) *
          g.pullbackVolumeDensity e x) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    dsimp only [g, B, c]
    have hscalar := R.scalar_scale (-τ) (neg_neg_of_pos hτ) (e x)
    rw [show s * -τ = 0 - s * τ by ring] at hscalar
    rw [R.pullbackVolumeDensity_scale hτ, hscalar,
      R.inverse_pullbackCoefficients_scale hτ (hD.mfderiv_injective (hOs hx))]
    simp only [map_smul, smul_eq_mul]
    field_simp [R.tau_pos.ne', hτ.ne']
  refine ⟨(hi.const_mul c).congr heq, ?_⟩
  dsimp only [g, l] at heq
  change (∫ x in O, _) ≤ 0
  rw [← integral_congr_ae heq, integral_const_mul]
  exact mul_nonpos_of_nonneg_of_nonpos hc hw

end PoincareConjecture.AncientRescaling
