import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Diffeomorph

variable {E A H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}




theorem exists_chart_extension_of_isCompact
    (e : OpenPartialHomeomorph E M) (hes : e.source = univ)
    (he : ContMDiffOn 𝓘(Real, E) I ∞ e e.source)
    (hei : ContMDiffOn I 𝓘(Real, E) ∞ e.symm e.target)
    (F : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    {K : Set E} (hK : IsCompact K) (hfix : ∀ x ∉ K, F x = x) :
    IsCompact (e '' K) ∧ e '' K ⊆ e.target ∧
      ∃ D : Diffeomorph I I M M ∞,
        (∀ x ∉ e '' K, D x = x) ∧ ∀ x, D (e x) = e (F x) := by
  have hs (x : E) : x ∈ e.source := hes ▸ mem_univ x
  let U : Opens M := ⟨e.target, e.open_target⟩
  let C : Diffeomorph 𝓘(Real, E) I E U ∞ := {
    toEquiv := {
      toFun := fun x => ⟨e x, e.map_source (hs x)⟩
      invFun := fun x => e.symm x
      left_inv := fun x => e.left_inv (hs x)
      right_inv := fun x => Subtype.ext (e.right_inv x.property) }
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact contMDiffOn_univ.mp (hes ▸ he)
    contMDiff_invFun := by
      intro x
      exact (hei.contMDiffAt (e.open_target.mem_nhds x.property)).comp x
        contMDiff_subtype_val.contMDiffAt }
  let G := (C.symm.trans F).trans C
  have hcompact : IsCompact (e '' K) :=
    hK.image_of_continuousOn (he.continuousOn.mono (fun x _ => hs x))
  have htarget : e '' K ⊆ e.target := image_subset_iff.mpr (fun x _ => e.map_source (hs x))
  have hGfix (x : U) (hx : (x : M) ∉ e '' K) : G x = x := by
    have hxK : e.symm x ∉ K := fun h => hx ⟨e.symm x, h, e.right_inv x.property⟩
    apply Subtype.ext
    change e (F (e.symm x)) = x
    rw [hfix _ hxK, e.right_inv x.property]
  obtain ⟨D, hD, hDfix⟩ := exists_extension_of_isCompact U G hcompact htarget hGfix
  refine ⟨hcompact, htarget, D, hDfix, ?_⟩
  intro x
  have h := hD (C x)
  change D (e x) = e (F (e.symm (e x))) at h
  simpa only [e.left_inv (hs x)] using h

end Diffeomorph
