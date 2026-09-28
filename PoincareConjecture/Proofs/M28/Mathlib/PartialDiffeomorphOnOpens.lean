import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace H' N]

def diffeomorphOnOpens
    (e : PartialDiffeomorph I J M N ∞)
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    (hV : (V : Set M) ⊆ e.source)
    (hW : e '' (V : Set M) = (W : Set N)) :
    V ≃ₘ⟮I, J⟯ W := by
  let L : V ≃ₜ W := e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hV hW
  have htarget : (W : Set N) ⊆ e.target := by
    intro y hy
    rw [← hW] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact e.toPartialEquiv.map_source (hV hx)
  refine {
    toEquiv := L.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff W (L : V → W)).mp
    intro x
    change ContMDiffAt I J ∞ (e ∘ (Subtype.val : V → M)) x
    exact ((e.contMDiffOn (x : M) (hV x.property)).contMDiffAt
      (e.open_source.mem_nhds (hV x.property))).comp x
        (contMDiff_subtype_val (I := I) (U := V) (n := ∞)).contMDiffAt
  · apply (ContMDiff.subtypeVal_comp_iff V (L.symm : W → V)).mp
    intro y
    change ContMDiffAt J I ∞ (e.symm ∘ (Subtype.val : W → N)) y
    exact ((e.symm.contMDiffOn (y : N) (htarget y.property)).contMDiffAt
      (e.open_target.mem_nhds (htarget y.property))).comp y
        (contMDiff_subtype_val (I := J) (U := W) (n := ∞)).contMDiffAt

@[simp] theorem diffeomorphOnOpens_apply
    (e : PartialDiffeomorph I J M N ∞)
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    (hV : (V : Set M) ⊆ e.source)
    (hW : e '' (V : Set M) = (W : Set N)) (x : V) :
    ((diffeomorphOnOpens e V W hV hW x : W) : N) = e (x : M) := rfl

@[simp] theorem diffeomorphOnOpens_symm_apply
    (e : PartialDiffeomorph I J M N ∞)
    (V : TopologicalSpace.Opens M) (W : TopologicalSpace.Opens N)
    (hV : (V : Set M) ⊆ e.source)
    (hW : e '' (V : Set M) = (W : Set N)) (y : W) :
    (((diffeomorphOnOpens e V W hV hW).symm y : V) : M) =
      e.symm (y : N) := rfl

def diffeomorphOnCanonicalSource
    (e : PartialDiffeomorph I J H N ∞)
    (V : TopologicalSpace.Opens H) [Nonempty V]
    (W : TopologicalSpace.Opens N)
    (hV : (V : Set H) ⊆ e.source)
    (hW : e '' (V : Set H) = (W : Set N)) :
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    V ≃ₘ⟮I, J⟯ W := by
  letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let L : V ≃ₜ W := e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hV hW
  have htarget : (W : Set N) ⊆ e.target := by
    intro y hy
    rw [← hW] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact e.toPartialEquiv.map_source (hV hx)
  have hsource : ContMDiff I I ∞ (Subtype.val : V → H) :=
    contMDiff_isOpenEmbedding (I := I) (n := ∞)
      V.isOpen.isOpenEmbedding_subtypeVal
  refine {
    toEquiv := L.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff W (L : V → W)).mp
    intro x
    change ContMDiffAt I J ∞ (e ∘ (Subtype.val : V → H)) x
    exact ((e.contMDiffOn (x : H) (hV x.property)).contMDiffAt
      (e.open_source.mem_nhds (hV x.property))).comp x hsource.contMDiffAt
  · have hraw : ContMDiff J I ∞
        ((Subtype.val : V → H) ∘ (L.symm : W → V)) := by
      intro y
      change ContMDiffAt J I ∞ (e.symm ∘ (Subtype.val : W → N)) y
      exact ((e.symm.contMDiffOn (y : N) (htarget y.property)).contMDiffAt
        (e.open_target.mem_nhds (htarget y.property))).comp y
          (contMDiff_subtype_val (I := J) (U := W) (n := ∞)).contMDiffAt
    exact ContMDiff.of_comp_isOpenEmbedding
      V.isOpen.isOpenEmbedding_subtypeVal hraw

@[simp] theorem diffeomorphOnCanonicalSource_apply
    (e : PartialDiffeomorph I J H N ∞)
    (V : TopologicalSpace.Opens H) [Nonempty V]
    (W : TopologicalSpace.Opens N)
    (hV : (V : Set H) ⊆ e.source)
    (hW : e '' (V : Set H) = (W : Set N)) (x : V) :
    ((diffeomorphOnCanonicalSource e V W hV hW x : W) : N) =
      e (x : H) := rfl

end PartialDiffeomorph
