import PoincareConjecture.Proofs.Horizon.Topology.Maps.Homeomorph.CompactSupport
import Mathlib.Geometry.Manifold.Diffeomorph










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}


theorem exists_extension_of_isCompact (U : Opens M)
    (F : Diffeomorph I I U U ∞) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ x : U, (x : M) ∉ K → F x = x) :
    ∃ D : Diffeomorph I I M M ∞,
      (∀ x : U, D x = (F x : M)) ∧ (∀ x : M, x ∉ K → D x = x) := by
  let e := F.toHomeomorph.extendOfIsCompact U.isOpen hK hKU hfix
  have he (x : U) : e x = (F x : M) :=
    Homeomorph.extendOfIsCompact_apply _ _ _ _ _ x
  have hefix (x : M) (hx : x ∉ K) : e x = x :=
    Homeomorph.extendOfIsCompact_apply_of_notMem _ _ _ _ _ hx
  have hsmooth (f : M → M) (J : Diffeomorph I I U U ∞)
      (hin : ∀ x : U, f x = (J x : M)) (hout : ∀ x : M, x ∉ K → f x = x) :
      ContMDiff I I ∞ f := by
    intro x
    by_cases hx : x ∈ U
    · apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
      have hf : (fun y : U => f y) = (fun y => (J y : M)) := funext hin
      rw [hf]
      exact (contMDiff_subtype_val.comp J.contMDiff).contMDiffAt
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have heq : f =ᶠ[𝓝 x] id := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
        exact hout y hy
      exact contMDiffAt_id.congr_of_eventuallyEq heq
  have hesymm (x : U) : e.symm x = (F.symm x : M) := by
    apply e.injective
    rw [e.apply_symm_apply, he]
    exact (congrArg Subtype.val (F.apply_symm_apply x)).symm
  have hesymmfix (x : M) (hx : x ∉ K) : e.symm x = x := by
    apply e.injective
    rw [e.apply_symm_apply, hefix x hx]
  let D : Diffeomorph I I M M ∞ :=
    { e.toEquiv with
      contMDiff_toFun := hsmooth e F he hefix
      contMDiff_invFun := hsmooth e.symm F.symm hesymm hesymmfix }
  exact ⟨D, he, hefix⟩

end Diffeomorph
