import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.TestRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Integral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem weakPairing_integrable_of_continuousOn
    (F : RicciFlow n M J) {α β : ℝ}
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β))
    (φ : testFunctions (n := n) (univ ×ˢ Ioo α β)) :
    (∀ τ, Integrable (fun x => u (x, τ) * testOperator F φ (x, τ))
      (F.metric (-τ)).volumeMeasure) ∧
    Integrable (fun τ => ∫ x, u (x, τ) * testOperator F φ (x, τ)
      ∂(F.metric (-τ)).volumeMeasure) := by
  let A := Prod.fst '' tsupport (φ : M × ℝ → ℝ)
  have hA : IsCompact A := φ.property.2.1.isCompact.image continuous_fst
  let f := fun z : M × ℝ => u z * testOperator F φ z
  have hf : ContinuousOn f (univ ×ˢ Icc α β) := hu.mul
    ((contMDiffOn_testOperator F φ.property.1).continuousOn.mono
      (fun z hz => ⟨mem_univ _, ht z.2 hz.2⟩))
  have hzA (τ : ℝ) (x : M) (hx : x ∉ A) : f (x, τ) = 0 := by
    have hs : (x, τ) ∉ tsupport (φ : M × ℝ → ℝ) :=
      fun h => hx (mem_image_of_mem Prod.fst h)
    dsimp only [f]
    rw [testOperator_eq_zero_of_notMem_tsupport F hs, mul_zero]
  have hzt (τ : ℝ) (hτ : τ ∉ Icc α β) (x : M) : f (x, τ) = 0 := by
    have hs : (x, τ) ∉ tsupport (φ : M × ℝ → ℝ) :=
      fun h => hτ ⟨(φ.property.2.2 h).2.1.le, (φ.property.2.2 h).2.2.le⟩
    dsimp only [f]
    rw [testOperator_eq_zero_of_notMem_tsupport F hs, mul_zero]
  constructor
  · intro τ
    by_cases hτ : τ ∈ Icc α β
    · have hc : Continuous (fun x => f (x, τ)) :=
        hf.comp_continuous (continuous_id.prodMk continuous_const)
          (fun x => ⟨mem_univ x, hτ⟩)
      have hs : Function.support (fun x => f (x, τ)) ⊆ A := by
        intro x hx
        by_contra hxA
        exact hx (hzA τ x hxA)
      exact (integrableOn_iff_integrable_of_support_subset hs).mp
        (hc.continuousOn.integrableOn_compact hA)
    · change Integrable (fun x => f (x, τ)) (F.metric (-τ)).volumeMeasure
      rw [show (fun x => f (x, τ)) = (fun _ => (0 : ℝ)) from funext (hzt τ hτ)]
      exact integrable_zero _ _ _
  · have hi := F.integrableOn_backward_integral_volumeMeasure_Icc_of_compact_support
      ht hA hf (fun τ _ x hx => hzA τ x hx)
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc α β) ?_).mp hi
    intro τ hτ
    by_contra ht'
    exact hτ (by simp only [hzt τ ht', integral_zero])

def weakPairingLinearOfContinuousOn
    (F : RicciFlow n M J) {α β : ℝ}
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β)) :
    testFunctions (n := n) ((univ : Set M) ×ˢ Ioo α β) →ₗ[ℝ] ℝ :=
  weakPairingLinear F u (univ ×ˢ Ioo α β)
    (fun φ => (weakPairing_integrable_of_continuousOn F ht hu φ).1)
    (fun φ => (weakPairing_integrable_of_continuousOn F ht hu φ).2)

end PoincareConjecture.RicciFlow.ConjugateHeat
