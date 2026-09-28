import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartCompression
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine











set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph






theorem locallyPiecewiseAffineOn_comp_supported_compression
    {D E F X : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph E X) (H : OpenPartialHomeomorph E E)
    (T : OpenPartialHomeomorph D X) {c : E} {K : Set E} {U : Set X}
    (hK : IsCompact K) (hKS : K ⊆ Q.source)
    (hHS : H.source = Q.source \ {c}) (hHT : H.target ⊆ Q.source)
    (hH : LocallyPiecewiseAffineOn H H.source)
    (hTQ : LocallyPiecewiseAffineOn (T.trans Q.symm) (T.trans Q.symm).source)
    (C : X → X)
    (hCchart : EqOn C (Q.symm.trans (H.trans Q)) (Q.symm.trans (H.trans Q)).source)
    (hCfix : EqOn C id (Q '' K)ᶜ)
    (himage : Q '' H.target ⊆ U) (houtside : (Q '' K)ᶜ ⊆ U)
    (f : X → F)
    (hFQ : LocallyPiecewiseAffineOn (f ∘ Q) (Q.source ∩ Q ⁻¹' U))
    (hFT : LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' U)) :
    LocallyPiecewiseAffineOn (f ∘ C ∘ T) (T.source ∩ T ⁻¹' {Q c}ᶜ) := by
  let e := Q.symm.trans (H.trans Q)
  let DQ := T.trans Q.symm
  let V := T.source ∩ T ⁻¹' {Q c}ᶜ
  let O := (Q '' K)ᶜ
  have hV : IsOpen V :=
    T.continuousOn_toFun.isOpen_inter_preimage T.open_source isClosed_singleton.isOpen_compl
  have hO : IsOpen O :=
    (hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)).isClosed.isOpen_compl
  have hES (z : X) (hzQ : z ∈ Q.target) (hz : z ∈ ({Q c} : Set X)ᶜ) :
      z ∈ e.source := by
    have hxH : Q.symm z ∈ H.source := by
      rw [hHS]
      refine ⟨Q.map_target hzQ, ?_⟩
      intro he
      have he' : Q.symm z = c := mem_singleton_iff.mp he
      exact hz (mem_singleton_iff.mpr ((Q.right_inv hzQ).symm.trans (congrArg Q he')))
    exact ⟨hzQ, hxH, hHT (H.map_source hxH)⟩
  have hinside := (hFQ.comp hH).comp hTQ
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  by_cases hzQ : T x ∈ Q.target
  · let N := (T.trans e).source
    have hxN : x ∈ N := ⟨hx.1, hES (T x) hzQ hx.2⟩
    refine ⟨N, hxN, ?_⟩
    have hsub : V ∩ N ⊆ DQ.source ∩ DQ ⁻¹'
        (H.source ∩ H ⁻¹' (Q.source ∩ Q ⁻¹' U)) := by
      intro y hy
      have hye : T y ∈ e.source := hy.2.2
      change (T y ∈ Q.target ∧ Q.symm (T y) ∈ H.source ∧
        H (Q.symm (T y)) ∈ Q.source) at hye
      refine ⟨⟨hy.2.1, hye.1⟩, hye.2.1, hye.2.2, ?_⟩
      exact himage ⟨H (Q.symm (T y)), H.map_source hye.2.1, rfl⟩
    apply (hinside.mono (hV.inter (T.trans e).open_source) hsub).congr
    intro y hy
    change f (Q (H (Q.symm (T y)))) = f (C (T y))
    exact congrArg f (hCchart hy.2.2).symm
  · have hzO : T x ∈ O := by
      rintro ⟨y, hyK, he⟩
      exact hzQ (he ▸ Q.map_source (hKS hyK))
    let N := T.source ∩ T ⁻¹' O
    have hN : IsOpen N := T.continuousOn_toFun.isOpen_inter_preimage T.open_source hO
    refine ⟨N, ⟨hx.1, hzO⟩, ?_⟩
    have hsub : V ∩ N ⊆ T.source ∩ T ⁻¹' U :=
      fun _ hy => ⟨hy.2.1, houtside hy.2.2⟩
    apply (hFT.mono (hV.inter hN) hsub).congr
    intro y hy
    change f (T y) = f (C (T y))
    exact congrArg f (hCfix hy.2.2).symm

end OpenPartialHomeomorph
