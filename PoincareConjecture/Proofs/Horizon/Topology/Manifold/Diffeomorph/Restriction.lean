import Mathlib.Geometry.Manifold.Diffeomorph








set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

def restrictOpens (D : Diffeomorph I I' M M' ∞) (U : Opens M) (V : Opens M')
    (hmem : ∀ x : M, D x ∈ V ↔ x ∈ U) : Diffeomorph I I' U V ∞ where
  toFun x := ⟨D x, (hmem x).mpr x.property⟩
  invFun y := ⟨D.symm y, (hmem (D.symm y)).mp (by simp)⟩
  left_inv x := Subtype.ext (D.symm_apply_apply x)
  right_inv y := Subtype.ext (D.apply_symm_apply y)
  contMDiff_toFun := by
    rw [← ContMDiff.subtypeVal_comp_iff V]
    exact D.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    rw [← ContMDiff.subtypeVal_comp_iff U]
    exact D.symm.contMDiff.comp contMDiff_subtype_val

@[simp] theorem restrictOpens_apply (D : Diffeomorph I I' M M' ∞)
    (U : Opens M) (V : Opens M') (hmem : ∀ x : M, D x ∈ V ↔ x ∈ U) (x : U) :
    (D.restrictOpens U V hmem x : M') = D x := rfl

@[simp] theorem restrictOpens_symm_apply (D : Diffeomorph I I' M M' ∞)
    (U : Opens M) (V : Opens M') (hmem : ∀ x : M, D x ∈ V ↔ x ∈ U) (y : V) :
    ((D.restrictOpens U V hmem).symm y : M) = D.symm y := rfl

theorem mem_iff_of_fixed_compl (D : Diffeomorph I I M M ∞) {S U : Set M}
    (hSU : S ⊆ U) (hfixed : ∀ x ∉ S, D x = x) (x : M) : D x ∈ U ↔ x ∈ U := by
  by_cases hx : x ∈ U
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    by_contra hDx
    have hDD : D (D x) = D x := hfixed _ (fun hS => hDx (hSU hS))
    have heq : D x = x := D.injective hDD
    exact hDx (heq.symm ▸ hx)
  · rw [hfixed x (fun hS => hx (hSU hS))]

def restrictOpensOfFixedCompl (D : Diffeomorph I I M M ∞) (U : Opens M)
    {S : Set M} (hSU : S ⊆ U) (hfixed : ∀ x ∉ S, D x = x) :
    Diffeomorph I I U U ∞ :=
  D.restrictOpens U U (D.mem_iff_of_fixed_compl hSU hfixed)

@[simp] theorem restrictOpensOfFixedCompl_apply (D : Diffeomorph I I M M ∞)
    (U : Opens M) {S : Set M} (hSU : S ⊆ U) (hfixed : ∀ x ∉ S, D x = x) (x : U) :
    (D.restrictOpensOfFixedCompl U hSU hfixed x : M) = D x := rfl

end Diffeomorph
