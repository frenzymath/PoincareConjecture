import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ContractionEndpoints











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem m60_exists_controlled_local_contraction
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ (C : ℝ × (M × M) → M) (U : Set (M × M)) (B : ℝ),
      IsOpen U ∧ diagonal M ⊆ U ∧ 0 ≤ B ∧
      (∀ p q, C (0, p, q) = q) ∧
      (∀ v ∈ U, C (1, v) = v.1) ∧
      (∀ t p, C (t, p, p) = p) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U, ∀ v : TangentSpace (𝓡 3) x.2.1,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, v, 0)) ≤
            B * g.tangentNorm x.2.1 v) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U, ∀ v : TangentSpace (𝓡 3) x.2.2,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, 0, v)) ≤
            B * g.tangentNorm x.2.2 v) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ p q, g.edist p q < ENNReal.ofReal delta → (p, q) ∈ U ∧
          ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (C (t, p, q))
            (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, p, q)
              (1, 0, 0)) < epsilon := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨C, U, hU, hdiag, h0, h1, hfix, hC⟩ :=
    Proofs.M58.exists_local_contraction (𝓡 3) hcompact 1
  obtain ⟨L, hL, hdiagL, hLU⟩ := exists_compact_between isCompact_diagonal hU hdiag
  have hCL : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x :=
    fun x hx => hC x ⟨hx.1, hLU hx.2⟩
  obtain ⟨B, hB, hp, hq⟩ := m60Contraction_endpointDerivative_bounds g hcompact C hL hCL
  have hCV : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ interior L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x :=
    fun x hx => hCL x ⟨hx.1, interior_subset hx.2⟩
  refine ⟨C, interior L, B, isOpen_interior, hdiagL, hB, h0,
    (fun v hv => h1 v (hLU (interior_subset hv))), hfix, hCV,
    (fun x hx => hp x ⟨hx.1, interior_subset hx.2⟩),
    (fun x hx => hq x ⟨hx.1, interior_subset hx.2⟩), ?_⟩
  intro epsilon hepsilon
  obtain ⟨V, hV, hdiagV, hVL, htime⟩ := m60Contraction_small_timeDerivative g hcompact C
    isOpen_interior hdiagL hfix hCV hepsilon
  obtain ⟨delta, hdelta, hpairs⟩ := Proofs.M58.exists_uniform_riemannian_radius g hcompact
    hV (fun p => hdiagV (show (p, p) ∈ diagonal M from rfl))
  refine ⟨delta, hdelta, ?_⟩
  intro p q hpq
  have hpqV := hpairs p q hpq
  exact ⟨hVL hpqV, fun t ht => htime (t, p, q) ⟨ht, hpqV⟩⟩

end PoincareConjecture
