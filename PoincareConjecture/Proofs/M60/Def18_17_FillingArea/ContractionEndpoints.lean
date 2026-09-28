import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ContractionTime










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in



theorem m60Contraction_swapped_derivative (C : ℝ × (M × M) → M)
    (x : ℝ × (M × M)) (v : TangentSpace (𝓡 3) x.2.2)
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (x.1, x.2.2, x.2.1)) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3)
      (fun y => C (y.1, y.2.2, y.2.1)) x (0, 0, v) =
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (x.1, x.2.2, x.2.1) (0, v, 0) := by
  have hs : MDifferentiableAt ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3))
      Prod.swap x.2 := mdifferentiableAt_snd.prodMk mdifferentiableAt_fst
  have hi : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (Prod.map id Prod.swap) x :=
    mdifferentiableAt_id.prodMap hs
  have hc := mfderiv_comp_apply x hC hi (0, 0, v)
  erw [mfderiv_prodMap mdifferentiableAt_id hs,
    mfderiv_prodMk mdifferentiableAt_snd mdifferentiableAt_fst,
    mfderiv_id, mfderiv_snd, mfderiv_fst] at hc
  exact hc




theorem m60Contraction_endpointDerivative_bounds [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    (C : ℝ × (M × M) → M) {L : Set (M × M)} (hL : IsCompact L)
    (hC : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L, ∀ v : TangentSpace (𝓡 3) x.2.1,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, v, 0)) ≤
            B * g.tangentNorm x.2.1 v) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L, ∀ v : TangentSpace (𝓡 3) x.2.2,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, 0, v)) ≤
            B * g.tangentNorm x.2.2 v) := by
  let C' := fun y : ℝ × (M × M) => C (y.1, y.2.2, y.2.1)
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) 1
      (fun y : ℝ × (M × M) => (y.1, y.2.2, y.2.1)) :=
    contMDiff_fst.prodMk (contMDiff_snd.snd.prodMk contMDiff_snd.fst)
  have hC' : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ (Prod.swap '' L),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C' x := by
    intro x hx
    have hpair : (x.2.2, x.2.1) ∈ L := by
      obtain ⟨p, hp, heq⟩ := hx.2
      simpa only [← heq, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap] using hp
    exact (hC (x.1, x.2.2, x.2.1) ⟨hx.1, hpair⟩).comp x hswap.contMDiffAt
  obtain ⟨_, Bq, _, hBq, _, hq⟩ :=
    Proofs.M58.exists_contraction_derivative_bounds g hcompact C hL hC
  obtain ⟨_, Bp, _, hBp, _, hp⟩ :=
    Proofs.M58.exists_contraction_derivative_bounds g hcompact C'
      (hL.image continuous_swap) hC'
  refine ⟨max Bp Bq, hBp.trans (le_max_left _ _), ?_, ?_⟩
  · intro x hx v
    have h := hp (x.1, x.2.2, x.2.1) ⟨hx.1, mem_image_of_mem Prod.swap hx.2⟩ v
    rw [show C' = (fun y => C (y.1, y.2.2, y.2.1)) from rfl,
      m60Contraction_swapped_derivative C _ v
        ((hC x hx).mdifferentiableAt one_ne_zero)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _))
  · intro x hx v
    exact (hq x hx v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.sqrt_nonneg _))

end PoincareConjecture
