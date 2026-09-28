import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Composition

















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

section TopologicalCompatibility

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]




theorem eqOn_chart_comparison_of_transition
    (e₀ e₁ : OpenPartialHomeomorph M P) (c₀ c₁ : OpenPartialHomeomorph N P)
    (htrans : EqOnSource (e₀.symm.trans e₁) (c₀.symm.trans c₁)) :
    EqOn (c₀.symm ∘ e₀) (c₁.symm ∘ e₁) (e₀.source ∩ e₁.source) := by
  intro x hx
  have he : e₀ x ∈ (e₀.symm.trans e₁).source := by
    rw [trans_source, symm_source]
    refine ⟨e₀.map_source hx.1, ?_⟩
    change e₀.symm (e₀ x) ∈ e₁.source
    rw [e₀.left_inv hx.1]
    exact hx.2
  have hc : e₀ x ∈ (c₀.symm.trans c₁).source := htrans.source_eq ▸ he
  rw [trans_source, symm_source] at hc
  have h := htrans.eqOn he
  change e₁ (e₀.symm (e₀ x)) = c₁ (c₀.symm (e₀ x)) at h
  rw [e₀.left_inv hx.1] at h
  change c₀.symm (e₀ x) = c₁.symm (e₁ x)
  rw [h, c₁.left_inv hc.2]

end TopologicalCompatibility

section SmoothCompatibility

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {M N P : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [TopologicalSpace P] [ChartedSpace H'' P] {n : ℕ∞ω}





theorem exists_diffeomorph_of_compatible
    (e₀ e₁ : OpenPartialHomeomorph M N)
    (hsource : e₀.source ∪ e₁.source = univ)
    (htarget : e₀.target ∪ e₁.target = univ)
    (he₀ : ContMDiffOn I J n e₀ e₀.source)
    (he₁ : ContMDiffOn I J n e₁ e₁.source)
    (hi₀ : ContMDiffOn J I n e₀.symm e₀.target)
    (hi₁ : ContMDiffOn J I n e₁.symm e₁.target)
    (hforward : EqOn e₀ e₁ (e₀.source ∩ e₁.source))
    (hinverse : EqOn e₀.symm e₁.symm (e₀.target ∩ e₁.target)) :
    ∃ d : Diffeomorph I J M N n,
      EqOn d e₀ e₀.source ∧ EqOn d e₁ e₁.source ∧
      EqOn d.symm e₀.symm e₀.target ∧ EqOn d.symm e₁.symm e₁.target := by
  classical
  let f : M → N := fun x => if x ∈ e₀.source then e₀ x else e₁ x
  let g : N → M := fun y => if y ∈ e₀.target then e₀.symm y else e₁.symm y
  have hf₀ : EqOn f e₀ e₀.source := fun x hx => if_pos hx
  have hf₁ : EqOn f e₁ e₁.source := by
    intro x hx
    by_cases hx₀ : x ∈ e₀.source
    · exact (if_pos hx₀).trans (hforward ⟨hx₀, hx⟩)
    · exact if_neg hx₀
  have hg₀ : EqOn g e₀.symm e₀.target := fun y hy => if_pos hy
  have hg₁ : EqOn g e₁.symm e₁.target := by
    intro y hy
    by_cases hy₀ : y ∈ e₀.target
    · exact (if_pos hy₀).trans (hinverse ⟨hy₀, hy⟩)
    · exact if_neg hy₀
  have hleft : Function.LeftInverse g f := by
    intro x
    have hx : x ∈ e₀.source ∪ e₁.source := hsource.symm ▸ mem_univ x
    rcases hx with hx | hx
    · rw [hf₀ hx, hg₀ (e₀.map_source hx), e₀.left_inv hx]
    · rw [hf₁ hx, hg₁ (e₁.map_source hx), e₁.left_inv hx]
  have hright : Function.RightInverse g f := by
    intro y
    have hy : y ∈ e₀.target ∪ e₁.target := htarget.symm ▸ mem_univ y
    rcases hy with hy | hy
    · rw [hg₀ hy, hf₀ (e₀.map_target hy), e₀.right_inv hy]
    · rw [hg₁ hy, hf₁ (e₁.map_target hy), e₁.right_inv hy]
  let d : Diffeomorph I J M N n :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := contMDiff_of_contMDiffOn_union_of_isOpen
        (he₀.congr hf₀) (he₁.congr hf₁) hsource e₀.open_source e₁.open_source
      contMDiff_invFun := contMDiff_of_contMDiffOn_union_of_isOpen
        (hi₀.congr hg₀) (hi₁.congr hg₁) htarget e₀.open_target e₁.open_target }
  exact ⟨d, hf₀, hf₁, hg₀, hg₁⟩





theorem exists_diffeomorph_of_chart_transition
    (e₀ e₁ : OpenPartialHomeomorph M P) (c₀ c₁ : OpenPartialHomeomorph N P)
    (hsource : e₀.source ∪ e₁.source = univ)
    (hcover : c₀.source ∪ c₁.source = univ)
    (htarget₀ : e₀.target = c₀.target) (htarget₁ : e₁.target = c₁.target)
    (he₀ : ContMDiffOn I K n e₀ e₀.source)
    (he₁ : ContMDiffOn I K n e₁ e₁.source)
    (hei₀ : ContMDiffOn K I n e₀.symm e₀.target)
    (hei₁ : ContMDiffOn K I n e₁.symm e₁.target)
    (hc₀ : ContMDiffOn J K n c₀ c₀.source)
    (hc₁ : ContMDiffOn J K n c₁ c₁.source)
    (hci₀ : ContMDiffOn K J n c₀.symm c₀.target)
    (hci₁ : ContMDiffOn K J n c₁.symm c₁.target)
    (htrans : EqOnSource (e₀.symm.trans e₁) (c₀.symm.trans c₁)) :
    ∃ d : Diffeomorph I J M N n,
      EqOn d (c₀.symm ∘ e₀) e₀.source ∧ EqOn d (c₁.symm ∘ e₁) e₁.source ∧
      EqOn d.symm (e₀.symm ∘ c₀) c₀.source ∧
      EqOn d.symm (e₁.symm ∘ c₁) c₁.source := by
  let g₀ := e₀.trans' c₀.symm htarget₀
  let g₁ := e₁.trans' c₁.symm htarget₁
  have hg₀ : ContMDiffOn I J n g₀ g₀.source :=
    hci₀.comp he₀ (fun x hx => htarget₀ ▸ e₀.map_source hx)
  have hg₁ : ContMDiffOn I J n g₁ g₁.source :=
    hci₁.comp he₁ (fun x hx => htarget₁ ▸ e₁.map_source hx)
  have hgi₀ : ContMDiffOn J I n g₀.symm g₀.target :=
    hei₀.comp hc₀ (fun x hx => htarget₀.symm ▸ c₀.map_source hx)
  have hgi₁ : ContMDiffOn J I n g₁.symm g₁.target :=
    hei₁.comp hc₁ (fun x hx => htarget₁.symm ▸ c₁.map_source hx)
  have hreverse : EqOnSource (c₀.symm.trans c₁) (e₀.symm.trans e₁) :=
    ⟨htrans.source_eq.symm, fun x hx => (htrans.eqOn (htrans.source_eq.symm ▸ hx)).symm⟩
  exact exists_diffeomorph_of_compatible g₀ g₁ hsource hcover hg₀ hg₁ hgi₀ hgi₁
    (eqOn_chart_comparison_of_transition e₀ e₁ c₀ c₁ htrans)
    (eqOn_chart_comparison_of_transition c₀ c₁ e₀ e₁ hreverse)

end SmoothCompatibility

end OpenPartialHomeomorph
