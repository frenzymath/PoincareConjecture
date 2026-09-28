import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.PairingIntegrability
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem tsupport_productTest_subset (χ : M → ℝ) (η : ℝ → ℝ) :
    tsupport (fun z : M × ℝ => χ z.1 * η z.2) ⊆ tsupport χ ×ˢ tsupport η := by
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport η))
  intro z hz
  exact ⟨subset_tsupport χ (mul_ne_zero_iff.mp hz).1,
    subset_tsupport η (mul_ne_zero_iff.mp hz).2⟩

def productTest {α β : ℝ} {χ : M → ℝ} {η : ℝ → ℝ}
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ioo α β) : testFunctions (n := n) ((univ : Set M) ×ˢ Ioo α β) :=
  ⟨fun z => χ z.1 * η z.2,
    (hχ.comp contMDiff_fst).mul (hη.contMDiff.comp contMDiff_snd),
    ((hχc.isCompact.prod hηc.isCompact).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_productTest_subset χ η)),
    (tsupport_productTest_subset χ η).trans (prod_mono (subset_univ _) hηs)⟩

theorem testOperator_product (F : RicciFlow n M J)
    {χ : M → ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (z : M × ℝ) :
    testOperator F (fun z => χ z.1 * η z.2) z =
      deriv η z.2 * χ z.1 + η z.2 * (F.connection (-z.2)).laplacian χ z.1 := by
  unfold testOperator
  dsimp only
  rw [deriv_const_mul _ (hη.differentiable (by simp) z.2)]
  have heq : (fun x => χ x * η z.2) = (fun x => η z.2 * χ x) :=
    funext (fun x => mul_comm _ _)
  rw [heq, (F.connection (-z.2)).laplacian_const_mul]
  rw [mul_comm (χ z.1)]

section Measure

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integral_productTest_operator
    (F : RicciFlow n M J) {u : M × ℝ → ℝ} {τ : ℝ}
    (hu : Continuous (fun x => u (x, τ)))
    {χ : M → ℝ} {η : ℝ → ℝ}
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ ∞ η) :
    (∫ x, u (x, τ) * testOperator F (fun z => χ z.1 * η z.2) (x, τ)
      ∂(F.metric (-τ)).volumeMeasure) =
      deriv η τ * (∫ x, u (x, τ) * χ x ∂(F.metric (-τ)).volumeMeasure) +
      η τ * (∫ x, u (x, τ) * (F.connection (-τ)).laplacian χ x
        ∂(F.metric (-τ)).volumeMeasure) := by
  have hi : Integrable (fun x => u (x, τ) * χ x) (F.metric (-τ)).volumeMeasure :=
    (hu.mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  have hj := (F.connection (-τ)).integrable_mul_laplacian_of_hasCompactSupport_right
    hu hχ hχc
  have heq : (fun x => u (x, τ) * testOperator F (fun z => χ z.1 * η z.2) (x, τ)) =
      (fun x => deriv η τ * (u (x, τ) * χ x) +
        η τ * (u (x, τ) * (F.connection (-τ)).laplacian χ x)) := by
    funext x
    rw [testOperator_product F hη]
    ring
  rw [heq, integral_add (hi.const_mul _) (hj.const_mul _), integral_const_mul,
    integral_const_mul]

end Measure
end PoincareConjecture.RicciFlow.ConjugateHeat
