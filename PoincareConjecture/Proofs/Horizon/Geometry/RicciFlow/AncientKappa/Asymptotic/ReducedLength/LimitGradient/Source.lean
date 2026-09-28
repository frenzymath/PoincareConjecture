import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Scaling

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

namespace AncientAsymptoticSolitonPredecessors

theorem regular_actual_reducedLength_gradient_bound
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    reducedLengthGradientNormSq K.flow 0
        (fun z => reducedLength K.flow 0 p z.1 z.2) τ q ≤
      3 * reducedLength K.flow 0 p q τ / τ := by
  have h := P.regular_reducedLength_gradient_bound r
  have hR := ((Classical.choice P.structural).structural M K).scalar_pos (0 - τ)
    (by linarith [r.tau_pos]) q
  have heq := regular_reducedLength_spatial_eventuallyEq r
  have hgrad : reducedLengthGradientNormSq K.flow 0
      (fun z => reducedLength K.flow 0 p z.1 z.2) τ q =
      reducedLengthGradientNormSq K.flow 0 r.representative τ q := by
    unfold reducedLengthGradientNormSq mvfderiv
    rw [heq.mfderiv_eq]
    rfl
  rw [hgrad]
  linarith

theorem reducedLength_coordinate_gradient_bound_ae
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    let g := K.flow.metric (0 - τ)
    let f := fun x => reducedLength K.flow 0 p (e x) τ
    ∀ᵐ x ∂volume, x ∈ e.source →
      fderiv ℝ f x ((g.pullbackCoefficients e x).inverse (fderiv ℝ f x)) ≤
        3 * f x / τ := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  filter_upwards [P.reducedLengthGradientNormSq_coordinates_ae p hτ e he hei,
    ae_regular_in_coordinates D hτ (by linarith) e he hei] with x hx hr hxs
  obtain ⟨r⟩ := D.regular_points (e x, τ) (hr hxs)
  rw [← hx hxs]
  exact P.regular_actual_reducedLength_gradient_bound r

end AncientAsymptoticSolitonPredecessors

namespace AncientRescaling

theorem reducedLength_coordinate_gradient_bound_ae
    {s : ℝ} (R : AncientRescaling K s) (P : AncientAsymptoticSolitonPredecessors K)
    (p : M) {τ : ℝ} (hτ : 0 < τ)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    let g := R.flow.metric (-τ)
    let f := fun x => reducedLength K.flow 0 p (e x) (s * τ)
    ∀ᵐ x ∂volume, x ∈ e.source →
      fderiv ℝ f x ((g.pullbackCoefficients e x).inverse (fderiv ℝ f x)) ≤
        3 * f x / τ := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  filter_upwards [P.reducedLength_coordinate_gradient_bound_ae p
    (mul_pos R.tau_pos hτ) e he hei] with x hx hxs
  rw [R.inverse_pullbackCoefficients_scale hτ (hD.mfderiv_injective hxs),
    map_smul, smul_eq_mul]
  calc
    _ ≤ s * (3 * reducedLength K.flow 0 p (e x) (s * τ) / (s * τ)) :=
      mul_le_mul_of_nonneg_left (hx hxs) R.tau_pos.le
    _ = _ := by field_simp [R.tau_pos.ne', hτ.ne']

end AncientRescaling
end PoincareConjecture
