import PoincareConjecture.Proofs.M58.Cor18_28_DiskExtension
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem continuous_contraction_time_input :
    Continuous (fun v : ℝ × (M × M) =>
      (⟨v, (1, 0, 0)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) := by
  have ht : Continuous (fun v : ℝ × (M × M) =>
      (⟨v.1, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_fst.prodMk continuous_const)
  have hp : Continuous (fun v : ℝ × (M × M) =>
      (⟨v.2, 0⟩ : TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hp)

theorem exists_contraction_derivative_bounds [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    (C : ℝ × (M × M) → M) {L : Set (M × M)} (hL : IsCompact L)
    (hC : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L, g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (1, 0, 0)) ≤ A) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L, ∀ v : TangentSpace (𝓡 3) x.2.2,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, 0, v)) ≤
            B * g.tangentNorm x.2.2 v) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
  have htime : ContinuousOn (fun x => ‖D x (1, 0, 0)‖) (Icc (0 : ℝ) 1 ×ˢ L) := by
    intro x hx
    exact (continuous_bundle_norm.continuousAt.comp
      ((continuousAt_tangentMap_of_contMDiffAt (hC x hx)).comp
        continuous_contraction_time_input.continuousAt)).continuousWithinAt
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod hL).exists_bound_of_continuousOn htime
  let Q : Set (TangentBundle (𝓡 3) M) := {v | v.proj ∈ (univ : Set M) ∧ ‖v.2‖ ≤ 1}
  have hQ : IsCompact Q := isCompact_bundle_norm_le hcompact 1
  let S : Set (ℝ × (M × TangentBundle (𝓡 3) M)) :=
    (Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Q)) ∩ {v | (v.2.1, v.2.2.proj) ∈ L}
  have hproj : Continuous (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      (v.2.1, v.2.2.proj)) := continuous_snd.fst.prodMk
        ((FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp continuous_snd.snd)
  have hS : IsCompact S := (isCompact_Icc.prod (hcompact.prod hQ)).inter_right
    (hL.isClosed.preimage hproj)
  have hlast : ContinuousOn (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      ‖D (v.1, v.2.1, v.2.2.proj) (0, 0, v.2.2.2)‖) S := by
    intro v hv
    exact (continuous_bundle_norm.continuousAt.comp
      ((continuousAt_tangentMap_of_contMDiffAt
        (hC (v.1, v.2.1, v.2.2.proj) ⟨hv.1.1, hv.2⟩)).comp
        continuous_contraction_tangent_input.continuousAt)).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hlast
  refine ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    exact (le_abs_self _).trans ((hA x hx).trans (le_max_left _ _))
  · intro x hx v
    change ‖D x (0, 0, v)‖ ≤ max B 0 * ‖v‖
    by_cases hv : v = 0
    · subst v
      change ‖D x 0‖ ≤ max B 0 * ‖(0 : TangentSpace (𝓡 3) x.2.2)‖
      erw [map_zero]
      simp
    · let w : TangentSpace (𝓡 3) x.2.2 := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
      have hmem : (x.1, x.2.1, (⟨x.2.2, w⟩ : TangentBundle (𝓡 3) M)) ∈ S :=
        ⟨⟨hx.1, mem_univ _, mem_univ _, hw.le⟩, hx.2⟩
      have hb : ‖D x (0, 0, w)‖ ≤ max B 0 :=
        (le_abs_self _).trans ((hB _ hmem).trans (le_max_left _ _))
      have heq : (0, 0, w) = ‖v‖⁻¹ •
          ((0, 0, v) : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) x) := by
        change (0, 0, w) = (‖v‖⁻¹ • (0 : ℝ), ‖v‖⁻¹ • (0 : LoopAmbient), ‖v‖⁻¹ • v)
        simp [w]
      erw [heq] at hb
      erw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))] at hb
      exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp (by simpa [div_eq_mul_inv, mul_comm] using hb)

theorem exists_bounded_local_contraction [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ (C : ℝ × (M × M) → M) (U : Set (M × M)) (A B : ℝ),
      IsOpen U ∧ diagonal M ⊆ U ∧ 0 ≤ A ∧ 0 ≤ B ∧
      (∀ p q, C (0, p, q) = q) ∧
      (∀ v ∈ U, C (1, v) = v.1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U, g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (1, 0, 0)) ≤ A) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U, ∀ v : TangentSpace (𝓡 3) x.2.2,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C x (0, 0, v)) ≤
            B * g.tangentNorm x.2.2 v) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨C, U, hU, hdiagU, h0, h1, -, hC⟩ := exists_local_contraction (𝓡 3) hcompact 1
  obtain ⟨L, hL, hdiagL, hLU⟩ := exists_compact_between isCompact_diagonal hU hdiagU
  have hCL : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C x :=
    fun x hx => hC x ⟨hx.1, hLU hx.2⟩
  obtain ⟨A, B, hA, hB, ht, hq⟩ := exists_contraction_derivative_bounds g hcompact C hL hCL
  refine ⟨C, interior L, A, B, isOpen_interior, hdiagL, hA, hB, h0, ?_, ?_, ?_, ?_⟩
  · exact fun v hv => h1 v (hLU (interior_subset hv))
  · exact fun x hx => hCL x ⟨hx.1, interior_subset hx.2⟩
  · exact fun x hx => ht x ⟨hx.1, interior_subset hx.2⟩
  · exact fun x hx => hq x ⟨hx.1, interior_subset hx.2⟩

end PoincareConjecture.Proofs.M58
