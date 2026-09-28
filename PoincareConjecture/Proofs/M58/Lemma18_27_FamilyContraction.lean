import PoincareConjecture.Proofs.M58.Sec18_4_ContractionEndpoints
import PoincareConjecture.Proofs.M58.Sec18_4_UniformRadius
import PoincareConjecture.Proofs.M58.Mathlib.LocalContraction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M58




theorem exists_short_family_contraction
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ ζ : ℝ, 0 < ζ ∧
      ∀ source : C(LoopTwoSphere, C1FreeLoopSpace (M := M)),
        (∀ c, freeLoopLength g (source c) < ζ) →
        ∃ H : C(I × LoopTwoSphere, C1FreeLoopSpace (M := M)),
          (∀ c, H (0, c) = source c) ∧
          (∀ c, H (1, c) = constantC1Loop (source c loopCircleBasepoint)) ∧
          ∀ t c p, source c = constantC1Loop p → H (t, c) = constantC1Loop p := by
  classical
  obtain ⟨C, U, hU, hdiagU, h0, h1, hdiag, hC⟩ :=
    exists_local_contraction (𝓡 3) hcompact 1
  obtain ⟨ζ, hζ, hshort⟩ := exists_short_loop_diagonal_radius g hcompact hU
    (fun p => hdiagU (by rfl : (p, p) ∈ diagonal M))
  refine ⟨ζ, hζ, ?_⟩
  intro source hlength
  let center : LoopTwoSphere → M := fun c => source c loopCircleBasepoint
  have hcenter : Continuous center :=
    (loopEvaluation loopCircleBasepoint).continuous.comp source.continuous
  have hpairs : ∀ c (z : LoopCircle), (center c, source c z) ∈ U :=
    fun c z => hshort (source c) (hlength c) z
  have hterminal : ∀ c (z : LoopCircle), C (1, center c, source c z) = center c :=
    fun c z => h1 _ (hpairs c z)
  have hregular : ∀ v : I × LoopTwoSphere, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (v.1, center v.2, source v.2 z) :=
    fun v z => hC _ ⟨v.1.property, hpairs v.2 z⟩
  let H : C(I × LoopTwoSphere, C1FreeLoopSpace (M := M)) :=
    ⟨fun v => endpointContractionLoop C v.1 (center v.2) (source v.2) (hregular v),
      continuous_endpointContractionLoop C h0 Prod.fst (center ∘ Prod.snd)
        (source ∘ Prod.snd) (fun v z => hterminal v.2 z) hregular
        continuous_fst (hcenter.comp continuous_snd) (source.continuous.comp continuous_snd)⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro c
    simp [H, endpointContractionLoop]
  · intro c
    simp [H, endpointContractionLoop, center]
  · intro t c p hconstant
    change endpointContractionLoop C t (source c loopCircleBasepoint) (source c) _ = _
    simp only [hconstant]
    exact endpointContractionLoop_constant C hdiag t p _

end PoincareConjecture.Proofs.M58
