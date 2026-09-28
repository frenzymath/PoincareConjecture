import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners Real E H} {J : ModelWithCorners Real F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [T2Space N] [Nonempty M]

omit [T2Space N] [Nonempty M] in

theorem isOpen_isLocalDiffeomorphAt {f : M -> N} :
    IsOpen {x | IsLocalDiffeomorphAt I J ∞ f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨e, hx, heq⟩
  apply mem_of_superset (e.open_source.mem_nhds hx)
  intro y hy
  exact ⟨e, hy, heq⟩

theorem exists_openPartialHomeomorph_of_injOn_compact
    {K : Set M} (hK : IsCompact K) {f : M -> N} (hinj : InjOn f K)
    (hloc : ∀ x ∈ K, IsLocalDiffeomorphAt I J ∞ f x) :
    ∃ e : OpenPartialHomeomorph M N,
      K ⊆ e.source ∧ f '' K ⊆ e.target ∧
      EqOn e f e.source ∧
      ContMDiffOn I J ∞ e e.source ∧
      ContMDiffOn J I ∞ e.symm e.target := by
  classical
  obtain ⟨V, hVo, hKV, hVinj⟩ := hinj.exists_isOpen_superset hK
    (fun x hx => (hloc x hx).contMDiffAt.continuousAt) (by
      intro x hx
      obtain ⟨e, he, heq⟩ := hloc x hx
      refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
      intro a ha b hb hab
      exact e.toPartialEquiv.injOn ha hb ((heq ha).symm.trans (hab.trans (heq hb))))
  let U : Opens M := ⟨V ∩ {x | IsLocalDiffeomorphAt I J ∞ f x},
    hVo.inter isOpen_isLocalDiffeomorphAt⟩
  have hKU : K ⊆ U := fun x hx => ⟨hKV hx, hloc x hx⟩
  have hUinj : InjOn f U := hVinj.mono inter_subset_left
  have hUloc : IsLocalDiffeomorph I J ∞ (fun x : U => f x) := by
    intro x
    exact (isLocalDiffeomorph_opensSubtypeVal I U x).comp J N x.property.2
  let p : PartialEquiv M N := hUinj.toPartialEquiv f U
  let e : OpenPartialHomeomorph M N :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict p
      (fun x hx => hx.2.contMDiffAt.continuousAt.continuousWithinAt)
      hUloc.isOpenMap U.isOpen
  have heq : (e : M -> N) = f := rfl
  have hsource : e.source = U := rfl
  have htarget : e.target = f '' U := rfl
  refine ⟨e, hKU, ?_, fun _ _ => rfl, ?_, ?_⟩
  · rw [htarget]
    exact image_mono hKU
  · intro x hx
    exact hx.2.contMDiffAt.contMDiffWithinAt
  · intro y hy
    let x := e.symm y
    have hx : x ∈ U := e.map_target hy
    have hf : IsLocalDiffeomorphAt I J ∞ f x := hx.2
    have hfx : f x = y := e.right_inv hy
    have hgerm : e.symm =ᶠ[𝓝 y] hf.localInverse := by
      have hc : ContinuousAt e.symm y := e.continuousAt_symm hy
      filter_upwards [e.open_target.mem_nhds hy,
        hc.preimage_mem_nhds (hf.localInverse.open_target.mem_nhds
          hf.localInverse_mem_target)] with z hz hzin
      exact (hf.localInverse_left_inv hzin).symm.trans
        (congrArg hf.localInverse (e.right_inv hz))
    have hi : ContMDiffAt J I ∞ hf.localInverse y := by
      rw [← hfx]
      exact hf.localInverse_contMDiffAt
    exact (hi.congr_of_eventuallyEq hgerm).contMDiffWithinAt

end Poincare
