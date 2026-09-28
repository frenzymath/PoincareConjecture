import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalLaplacian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem principalFormPairing_add_right (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (w u v : dirichletForm K) :
    principalFormPairing K A w (u + v) =
      principalFormPairing K A w u + principalFormPairing K A w v := by
  simp only [principalFormPairing, principalEnergy, map_add, inner_add_right,
    Finset.sum_add_distrib]
  ring

private theorem principal_initial_variational {K : Set V} (hK : IsClosed K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (f : supportedTests K)
    {U B : dirichletValue K}
    (h : ∃ v : dirichletForm K, dirichletInclusion K v = U ∧
      ∀ w : dirichletForm K, principalFormPairing K A w v =
        inner ℝ (dirichletInclusion K w) (U + B)) :
    ∃ v : dirichletForm K, dirichletInclusion K v = intoDirichletValue K f + U ∧
      ∀ w : dirichletForm K, principalFormPairing K A w v =
        inner ℝ (dirichletInclusion K w)
          ((intoDirichletValue K f + U) +
            (-intoDirichletValue K (principalTestLaplacian hK A f) + B)) := by
  obtain ⟨v, hv, hp⟩ := h
  refine ⟨intoDirichletForm K f + v, ?_, ?_⟩
  · rw [map_add, dirichletInclusion_into, hv]
  · intro w
    rw [principalFormPairing_add_right, principalForm_pairing_laplacian hK A f w, hp w]
    simp only [inner_add_right, inner_sub_right, inner_neg_right]
    ring



theorem exists_principal_initial_heat {K : Set V} (hK : IsCompact K)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A i j x = A j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    {T : ℝ} (hT : 0 ≤ T) (f : supportedTests K) :
    ∃ U D B : ℝ → dirichletValue K,
      U 0 = intoDirichletValue K f ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (SpectralHeatNative.timeMeasure T) ∧
      MemLp B 2 (SpectralHeatNative.timeMeasure T) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, D t + B t = 0) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
        ∃ v : dirichletForm K, dirichletInclusion K v = U t ∧
          ∀ w : dirichletForm K, principalFormPairing K A w v =
            inner ℝ (dirichletInclusion K w) (U t + B t)) := by
  let L := intoDirichletValue K (principalTestLaplacian hK.isClosed A f)
  obtain ⟨W, D, B, hW0, hWcont, hD, hB, hd, heq, hgraph⟩ :=
    exists_principal_dirichlet_response hK A hEll hA hell hT
      (memLp_const L : MemLp (fun _ : ℝ => L) 2 (SpectralHeatNative.timeMeasure T))
  refine ⟨fun t => intoDirichletValue K f + W t, D, fun t => -L + B t,
    by simpa only [add_zero] using congrArg (fun z => intoDirichletValue K f + z) hW0,
    continuousOn_const.add hWcont, hD, (memLp_const (-L)).add hB, ?_, ?_, ?_⟩
  · filter_upwards [hd] with t ht
    simpa only [zero_add] using! (hasDerivAt_const t (intoDirichletValue K f)).add ht
  · filter_upwards [heq] with t ht
    calc
      D t + (-L + B t) = -L + (D t + B t) := by abel
      _ = 0 := by rw [ht, neg_add_cancel]
  · filter_upwards [hgraph] with t ht
    exact principal_initial_variational hK.isClosed A f ht



theorem principal_generator_weak_heat {K : Set V}
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {U D : dirichletValue K}
    (hgraph : ∃ v : dirichletForm K, dirichletInclusion K v = U ∧
      ∀ w : dirichletForm K, principalFormPairing K A w v =
        inner ℝ (dirichletInclusion K w) (U - D)) :
    ∃ v : dirichletForm K, dirichletInclusion K v = U ∧
      ∀ φ : supportedTests K,
        inner ℝ (intoDirichletValue K φ) D =
          -principalEnergy K A (intoDirichletForm K φ) v := by
  obtain ⟨v, hv, hp⟩ := hgraph
  refine ⟨v, hv, ?_⟩
  intro φ
  have h := hp (intoDirichletForm K φ)
  simp only [principalFormPairing, dirichletInclusion_into, inner_sub_right, hv] at h
  linarith only [h]

end PoincareConjecture.M35.Uniqueness.Heat
