import PoincareConjecture.Proofs.M58.Cor18_28_UniformBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in



theorem m60Contraction_timeDerivative_zero (C : ℝ × (M × M) → M)
    (hfix : ∀ t p, C (t, p, p) = p) (t : ℝ) (p : M)
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, p, p)) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, p, p) (1, 0, 0) = 0 := by
  have hinput : MDifferentiableAt 𝓘(ℝ, ℝ)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (fun s : ℝ => (s, p, p)) t :=
    mdifferentiableAt_id.prodMk (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
  have hc := mfderiv_comp_apply t hC hinput (1 : ℝ)
  have heq : C ∘ (fun s : ℝ => (s, p, p)) = fun _ : ℝ => p := funext (fun s => hfix s p)
  rw [heq, mfderiv_const] at hc
  erw [mfderiv_prodMk mdifferentiableAt_id
    (mdifferentiableAt_const.prodMk mdifferentiableAt_const),
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_const] at hc
  simp only [mfderiv_id, mfderiv_const] at hc
  exact hc.symm




theorem m60Contraction_timeNorm_continuousAt (g : RiemannianMetric 3 M)
    {C : ℝ × (M × M) → M} {x : ℝ × (M × M)}
    (hC : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x) :
    ContinuousAt (fun y => g.tangentNorm (C y)
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C y (1, 0, 0))) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  change ContinuousAt (fun y =>
    ‖mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C y (1, 0, 0)‖) x
  exact Proofs.M58.continuous_bundle_norm.continuousAt.comp
    ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt hC).comp
      Proofs.M58.continuous_contraction_time_input.continuousAt)




theorem m60Contraction_small_timeDerivative [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    (C : ℝ × (M × M) → M) {U : Set (M × M)} (hU : IsOpen U)
    (hdiag : diagonal M ⊆ U) (hfix : ∀ t p, C (t, p, p) = p)
    (hC : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ V : Set (M × M), IsOpen V ∧ diagonal M ⊆ V ∧ V ⊆ U ∧
      ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ V, g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (1, 0, 0)) < epsilon := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := fun x => g.tangentNorm (C x)
    (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (1, 0, 0))
  let W := interior {x | A x < epsilon}
  have hW : Icc (0 : ℝ) 1 ×ˢ diagonal M ⊆ W := by
    rintro ⟨t, p, q⟩ ⟨ht, hpq⟩
    have hpq' : p = q := hpq
    subst q
    have hc := hC (t, p, p) ⟨ht, hdiag rfl⟩
    have hzero : A (t, p, p) = 0 := by
      dsimp only [A]
      rw [m60Contraction_timeDerivative_zero C hfix t p (hc.mdifferentiableAt one_ne_zero)]
      change ‖(0 : TangentSpace (𝓡 3) (C (t, p, p)))‖ = 0
      exact norm_zero
    apply mem_interior_iff_mem_nhds.mpr
    exact (m60Contraction_timeNorm_continuousAt g hc).preimage_mem_nhds
      (isOpen_Iio.mem_nhds (by change A (t, p, p) < epsilon; rwa [hzero]))
  obtain ⟨T, V, _, hV, hT, hVdiag, hTV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_diagonal isOpen_interior hW
  refine ⟨V ∩ U, hV.inter hU, subset_inter hVdiag hdiag, inter_subset_right, ?_⟩
  intro x hx
  have hxW : x ∈ {y | A y < epsilon} := interior_subset (hTV ⟨hT hx.1, hx.2.1⟩)
  exact hxW

end PoincareConjecture
