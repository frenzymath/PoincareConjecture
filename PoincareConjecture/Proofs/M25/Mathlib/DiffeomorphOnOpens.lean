import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Composition











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe uK uE uF uH uH' uM uN

namespace Diffeomorph

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}




theorem exists_openPartialHomeomorph_of_opens
    {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}
    (d : Diffeomorph I J U V n) (hU : Nonempty U) :
    ∃ e : OpenPartialHomeomorph M N,
      e.source = (U : Set M) ∧ e.target = (V : Set N) ∧
      ContMDiffOn I J n e e.source ∧
      ContMDiffOn J I n e.symm e.target ∧
      (∀ (x : M) (hx : x ∈ (U : Set M)), e x = (d ⟨x, hx⟩).val) ∧
      (∀ (y : N) (hy : y ∈ (V : Set N)), e.symm y = (d.symm ⟨y, hy⟩).val) := by
  classical
  let hV : Nonempty V := hU.map d
  let eU := U.openPartialHomeomorphSubtypeCoe hU
  let eV := V.openPartialHomeomorphSubtypeCoe hV
  let eD := d.toHomeomorph.toOpenPartialHomeomorph
  let e := (eU.symm.trans eD).trans eV
  have hs : e.source = (U : Set M) := by
    simp only [e, OpenPartialHomeomorph.trans_source, eU, eV, eD,
      OpenPartialHomeomorph.symm_source,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  have ht : e.target = (V : Set N) := by
    simp only [e, OpenPartialHomeomorph.trans_target, eU, eV, eD,
      OpenPartialHomeomorph.symm_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
      Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]
  have hUi (x : M) (hx : x ∈ (U : Set M)) : eU.symm x = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact eU.right_inv ((U.openPartialHomeomorphSubtypeCoe_target hU).symm ▸ hx)
  have hVi (y : N) (hy : y ∈ (V : Set N)) : eV.symm y = ⟨y, hy⟩ := by
    apply Subtype.ext
    exact eV.right_inv ((V.openPartialHomeomorphSubtypeCoe_target hV).symm ▸ hy)
  have hf (x : M) (hx : x ∈ (U : Set M)) : e x = (d ⟨x, hx⟩).val := by
    change (d (eU.symm x)).val = (d ⟨x, hx⟩).val
    rw [hUi x hx]
  have hi (y : N) (hy : y ∈ (V : Set N)) :
      e.symm y = (d.symm ⟨y, hy⟩).val := by
    change (d.symm (eV.symm y)).val = (d.symm ⟨y, hy⟩).val
    rw [hVi y hy]
  have hfSub : ContMDiff I J n (fun x : U => e x.val) := by
    have h := (contMDiff_subtype_val (I := J) (U := V) (n := n)).comp d.contMDiff
    exact h.congr (fun x => hf x.val x.property)
  have hiSub : ContMDiff J I n (fun y : V => e.symm y.val) := by
    have h := (contMDiff_subtype_val (I := I) (U := U) (n := n)).comp d.symm.contMDiff
    exact h.congr (fun y => hi y.val y.property)
  refine ⟨e, hs, ht, ?_, ?_, hf, hi⟩
  · intro x hx
    have hxU : x ∈ (U : Set M) := hs ▸ hx
    have hAt : ContMDiffAt I J n e x :=
      (contMDiffAt_subtype_iff (U := U) (f := (e : M → N))
        (x := ⟨x, hxU⟩)).mp hfSub.contMDiffAt
    exact hAt.contMDiffWithinAt
  · intro y hy
    have hyV : y ∈ (V : Set N) := ht ▸ hy
    have hAt : ContMDiffAt J I n e.symm y :=
      (contMDiffAt_subtype_iff (U := V) (f := (e.symm : N → M))
        (x := ⟨y, hyV⟩)).mp hiSub.contMDiffAt
    exact hAt.contMDiffWithinAt

end Diffeomorph
