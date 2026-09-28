import PoincareConjecture.Proofs.M58.Sec18_4_ContractionLoops










set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem continuous_contraction_tangent_input :
    Continuous (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      (⟨(v.1, v.2.1, v.2.2.proj), (0, 0, v.2.2.2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) := by
  have ht : Continuous (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      (⟨v.1, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_fst
  have hp : Continuous (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      (⟨v.2.1, 0⟩ : TangentBundle (𝓡 3) M)) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_snd.fst
  have hpair : Continuous (fun v : ℝ × (M × TangentBundle (𝓡 3) M) =>
      (⟨(v.2.1, v.2.2.proj), (0, v.2.2.2)⟩ :
        TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓡 3) (I' := 𝓡 3)
      (M := M) (M' := M) (n := 0)).continuous.comp (hp.prodMk continuous_snd.snd)
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 3).prod (𝓡 3)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hpair)




theorem continuous_contractionLoop {X : Type v} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) (t : X → ℝ) (p : X → M)
    (γ : X → C1FreeLoopSpace (M := M))
    (hC : ∀ x (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t x, p x, γ x z))
    (ht : Continuous t) (hp : Continuous p) (hγ : Continuous γ) :
    Continuous (fun x => contractionLoop C (t x) (p x) (γ x) (hC x)) := by
  have hvalues : Continuous (fun v : X × LoopCircle => γ v.1 v.2) :=
    continuous_loop_eval.comp ((hγ.comp continuous_fst).prodMk continuous_snd)
  have hinput : Continuous (fun v : X × LoopCircle => (t v.1, p v.1, γ v.1 v.2)) :=
    (ht.comp continuous_fst).prodMk ((hp.comp continuous_fst).prodMk hvalues)
  have hvaluesC : Continuous (fun v : X × LoopCircle => C (t v.1, p v.1, γ v.1 v.2)) :=
    continuous_iff_continuousAt.mpr fun v =>
      (hC v.1 v.2).continuousAt.comp
        (f := fun w : X × LoopCircle => (t w.1, p w.1, γ w.1 w.2)) hinput.continuousAt
  have htangents : Continuous (fun v : X × LoopCircle => c1LoopTangent (γ v.1) v.2) :=
    continuous_loop_tangent_eval.comp ((hγ.comp continuous_fst).prodMk continuous_snd)
  have htinput : Continuous (fun v : X × LoopCircle =>
      (⟨(t v.1, p v.1, γ v.1 v.2), (0, 0, (c1LoopTangent (γ v.1) v.2).2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (ℝ × (M × M)))) :=
    continuous_contraction_tangent_input.comp
      ((ht.comp continuous_fst).prodMk ((hp.comp continuous_fst).prodMk htangents))
  have htangentsC : Continuous (fun v : X × LoopCircle =>
      tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        ⟨(t v.1, p v.1, γ v.1 v.2), (0, 0, (c1LoopTangent (γ v.1) v.2).2)⟩) :=
    continuous_iff_continuousAt.mpr fun v =>
      (continuousAt_tangentMap_of_contMDiffAt (hC v.1 v.2)).comp htinput.continuousAt
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun v : X × LoopCircle =>
      contractionLoop C (t v.1) (p v.1) (γ v.1) (hC v.1) v.2)
    simpa only [contractionLoop_apply] using hvaluesC
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun v : X × LoopCircle =>
      c1LoopTangent (contractionLoop C (t v.1) (p v.1) (γ v.1) (hC v.1)) v.2)
    simpa only [contractionLoop_tangent] using htangentsC

end PoincareConjecture.Proofs.M58
