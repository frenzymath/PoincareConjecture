import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.NormalMotion
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh

theorem supported_chart_transition_PL
    {E V X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph E X) (A B : OpenPartialHomeomorph V X)
    (H : E ≃ₜ E) (F : X ≃ₜ X)
    {K : Set E} (hK : IsCompact K) (hKS : K ⊆ Q.source)
    (hHfix : EqOn H id Kᶜ)
    (hFQ : EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target)
    (hFout : EqOn F id (Q '' K)ᶜ)
    (hHPL : H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E)
    (hAQ : LocallyPiecewiseAffineOn (A.trans Q.symm) (A.trans Q.symm).source)
    (hQB : LocallyPiecewiseAffineOn (Q.trans B.symm) (Q.trans B.symm).source)
    (hAB : A.trans B.symm ∈ piecewiseAffineGroupoid V) :
    A.trans (F.toOpenPartialHomeomorph.trans B.symm) ∈ piecewiseAffineGroupoid V := by
  let T := A.trans (F.toOpenPartialHomeomorph.trans B.symm)
  let D := A.trans Q.symm
  let C := Q.trans B.symm
  let G := D.trans (H.toOpenPartialHomeomorph.trans C)
  have hHS : MapsTo H Q.source Q.source := by
    intro x hx
    by_contra hn
    have hnotK : H x ∉ K := fun h => hn (hKS h)
    have he : H x = x := H.injective (hHfix hnotK)
    exact hn (he.symm ▸ hx)
  have hO : IsOpen (Q '' K)ᶜ :=
    (hK.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)).isClosed.isOpen_compl
  have hGPL : LocallyPiecewiseAffineOn G G.source :=
    (hQB.comp ((mem_piecewiseAffineGroupoid_iff E _).mp hHPL).1).comp hAQ
  have hABPL := (mem_piecewiseAffineGroupoid_iff V (A.trans B.symm)).mp hAB |>.1
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
  · have hxO : A x ∈ (Q '' K)ᶜ := by
      rintro ⟨y, hy, he⟩
      exact hxQ (he ▸ Q.map_source (hKS hy))
    let W := A.source ∩ A ⁻¹' (Q '' K)ᶜ
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

theorem supported_chart_moved_set
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (Q : OpenPartialHomeomorph E X) (H : E ≃ₜ E) (F : X ≃ₜ X)
    {K : Set E} (hKS : K ⊆ Q.source) (hHfix : EqOn H id Kᶜ)
    (hFQ : EqOn F (Q.symm.trans (H.toOpenPartialHomeomorph.trans Q)) Q.target)
    {S : Set X} {P : Set E}
    (hS : ∀ z ∈ Q.source, Q z ∈ S ↔ z ∈ P) :
    ∀ z ∈ Q.source, Q z ∈ F '' S ↔ z ∈ H '' P := by
  intro z hz
  have hHz : H.symm z ∈ Q.source := by
    by_contra hn
    have hnotK : H.symm z ∉ K := fun h => hn (hKS h)
    have heq : H.symm z = z := (hHfix hnotK).symm.trans (H.apply_symm_apply z)
    exact hn (heq.symm ▸ hz)
  have hFHz : F (Q (H.symm z)) = Q z := by
    have h := hFQ (Q.map_source hHz)
    change F (Q (H.symm z)) = Q (H (Q.symm (Q (H.symm z)))) at h
    rw [Q.left_inv hHz, H.apply_symm_apply] at h
    exact h
  have hmem : Q z ∈ F '' S ↔ Q (H.symm z) ∈ S := by
    constructor
    · rintro ⟨x, hx, heq⟩
      exact F.injective (heq.trans hFHz.symm) ▸ hx
    · exact fun hx => ⟨_, hx, hFHz⟩
  rw [hmem, hS _ hHz]
  constructor
  · exact fun h => ⟨_, h, H.apply_symm_apply z⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [H.symm_apply_apply] using hx

end PoincareConjecture.M76.CollarMesh
