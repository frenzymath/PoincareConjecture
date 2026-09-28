import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse











set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph





theorem supported_chart_transition_mem_piecewiseAffineGroupoid
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (Q A B : OpenPartialHomeomorph E X) (H : E ≃ₜ E) (F : X ≃ₜ X)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ Q.source)
    (hHfix : EqOn H id Kᶜ)
    (hFQ : EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target)
    (hFout : EqOn F id (Q '' K)ᶜ)
    (hHPL : H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E)
    (hAQ : A.trans Q.symm ∈ piecewiseAffineGroupoid E)
    (hBQ : B.trans Q.symm ∈ piecewiseAffineGroupoid E)
    (hAB : A.trans B.symm ∈ piecewiseAffineGroupoid E) :
    A.trans (F.toOpenPartialHomeomorph.trans B.symm) ∈ piecewiseAffineGroupoid E := by
  let T := A.trans (F.toOpenPartialHomeomorph.trans B.symm)
  let D := A.trans Q.symm
  let C := Q.trans B.symm
  let G := D.trans (H.toOpenPartialHomeomorph.trans C)
  let O := (Q '' K)ᶜ
  have hHS : MapsTo H Q.source Q.source := by
    intro x hx
    by_contra hn
    have hnotK : H x ∉ K := fun h => hn (hKS h)
    have he : H x = x := H.injective (hHfix hnotK)
    exact hn (he.symm ▸ hx)
  have hO : IsOpen O :=
    (hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)).isClosed.isOpen_compl
  have hCPL : C ∈ piecewiseAffineGroupoid E :=
    (piecewiseAffineGroupoid E).symm hBQ
  have hGPL : LocallyPiecewiseAffineOn G G.source :=
    (mem_piecewiseAffineGroupoid_iff E G).mp
      ((piecewiseAffineGroupoid E).trans hAQ
        ((piecewiseAffineGroupoid E).trans hHPL hCPL)) |>.1
  have hABPL := (mem_piecewiseAffineGroupoid_iff E (A.trans B.symm)).mp hAB |>.1
  apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  by_cases hxQ : A x ∈ Q.target
  · refine ⟨D.source, ⟨hx.1, hxQ⟩, ?_⟩
    have hsub : T.source ∩ D.source ⊆ G.source := by
      intro y hy
      refine ⟨hy.2, mem_univ _, hHS (Q.map_target hy.2.2), ?_⟩
      have hval : F (A y) = Q (H (Q.symm (A y))) := hFQ hy.2.2
      change Q (H (Q.symm (A y))) ∈ B.target
      rw [← hval]
      exact hy.1.2.2
    apply (hGPL.mono (T.open_source.inter D.open_source) hsub).congr
    intro y hy
    change B.symm (Q (H (Q.symm (A y)))) = B.symm (F (A y))
    exact congrArg B.symm (hFQ hy.2.2).symm
  · have hxO : A x ∈ O := by
      rintro ⟨y, hy, he⟩
      exact hxQ (he ▸ Q.map_source (hKS hy))
    let W := A.source ∩ A ⁻¹' O
    have hW : IsOpen W := A.continuousOn_toFun.isOpen_inter_preimage A.open_source hO
    refine ⟨W, ⟨hx.1, hxO⟩, ?_⟩
    have hsub : T.source ∩ W ⊆ (A.trans B.symm).source := by
      intro y hy
      refine ⟨hy.1.1, ?_⟩
      have hval : F (A y) = A y := hFout hy.2.2
      change A y ∈ B.target
      rw [← hval]
      exact hy.1.2.2
    apply (hABPL.mono (T.open_source.inter hW) hsub).congr
    intro y hy
    change B.symm (A y) = B.symm (F (A y))
    exact congrArg B.symm (hFout hy.2.2).symm

end OpenPartialHomeomorph
