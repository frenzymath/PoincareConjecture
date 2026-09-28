import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCover
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M25.Topology3D

theorem exists_puncturedProjective_cover_of_odd_partialHomeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {pOld pNew : RealProjectiveThree} {U V : Set M}
    (P : PoincareConjecture.StandardPuncturedProjectiveCover M pOld U)
    (H : OpenPartialHomeomorph UnitThreeSphere UnitThreeSphere)
    (hsource : H.source = projectiveCoverDomain pNew)
    (htarget : H.target = projectiveCoverDomain pOld ∩ P.cover ⁻¹' V)
    (hV : V ⊆ U)
    (hH : ContMDiffOn (𝓡 3) (𝓡 3) ∞ H H.source)
    (hHi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ H.symm H.target)
    (hodd : ∀ x ∈ H.source, H (-x) = -H x) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover M pNew V) := by
  have hmap {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain pNew) :
      H x ∈ projectiveCoverDomain pOld ∧ P.cover (H x) ∈ V := by
    have hh := H.map_source (hsource.symm ▸ hx)
    rw [htarget] at hh
    exact hh
  let dH : PartialDiffeomorph (𝓡 3) (𝓡 3)
      UnitThreeSphere UnitThreeSphere ∞ :=
    { toPartialEquiv := H.toPartialEquiv
      open_source := H.open_source
      open_target := H.open_target
      contMDiffOn_toFun := hH
      contMDiffOn_invFun := hHi }
  refine ⟨{
    cover := P.cover ∘ H
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmap hx).2
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := P.image_eq.symm.subset (hV hy)
      have hzt : z ∈ H.target := by
        rw [htarget]
        exact ⟨hz, by change P.cover z ∈ V; rw [hzy]; exact hy⟩
      refine ⟨H.symm z, ?_, ?_⟩
      · change H.symm z ∈ projectiveCoverDomain pNew
        rw [← hsource]
        exact H.map_target hzt
      · change P.cover (H (H.symm z)) = y
        rw [H.right_inv hzt, hzy]
  · intro x y hx hy
    have hxs : x ∈ H.source := hsource.symm ▸ hx
    have hys : y ∈ H.source := hsource.symm ▸ hy
    have hnys : -y ∈ H.source :=
      hsource.symm ▸ (neg_mem_projectiveCoverDomain_iff pNew y).mpr hy
    change P.cover (H x) = P.cover (H y) ↔ x = y ∨ x = -y
    rw [P.fibers (H x) (H y) (hmap hx).1 (hmap hy).1]
    constructor
    · rintro (hxy | hxy)
      · exact Or.inl (H.injOn hxs hys hxy)
      · exact Or.inr (H.injOn hxs hnys (hxy.trans (hodd y hys).symm))
    · rintro (hxy | hxy)
      · exact Or.inl (congrArg H hxy)
      · exact Or.inr ((congrArg H hxy).trans (hodd y hys))
  · intro x
    have hHx : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ H x :=
      ⟨dH, hsource.symm ▸ x.property, fun _ _ => rfl⟩
    exact hHx.comp (𝓡 3) M (P.local_diffeomorph ⟨H x, (hmap x.property).1⟩)

theorem standardPuncturedProjectiveCover_nonempty_corestrict_opens
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {p : PoincareConjecture.RealProjectiveThree} {V : Set M}
    (P : PoincareConjecture.StandardPuncturedProjectiveCover M p V)
    (U : TopologicalSpace.Opens M)
    (hV : V ⊆ (U : Set M)) (y0 : U) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover
      U p ((Subtype.val : U → M) ⁻¹' V)) := by
  classical
  let G : UnitThreeSphere → U := fun x =>
    if hx : P.cover x ∈ (U : Set M) then ⟨P.cover x, hx⟩ else y0
  have hG {x : UnitThreeSphere} (hx : P.cover x ∈ (U : Set M)) :
      (G x).val = P.cover x := by simp only [G, dif_pos hx]
  have hmem {x : UnitThreeSphere} (hx : x ∈ projectiveCoverDomain p) :
      P.cover x ∈ (U : Set M) :=
    hV (StandardPuncturedProjectiveCover.cover_mem P hx)
  refine ⟨{
    cover := G
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (G x).val ∈ V
      rw [hG (hmem hx)]
      exact StandardPuncturedProjectiveCover.cover_mem P hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := P.image_eq.symm.subset hy
      exact ⟨x, hx, Subtype.ext ((hG (hmem hx)).trans hxy)⟩
  · intro x y hx hy
    rw [Subtype.ext_iff, hG (hmem hx), hG (hmem hy)]
    exact P.fibers x y hx hy
  · intro x
    have hxP := P.local_diffeomorph x
    have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U (G x)
    have hinv : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        hi.localInverse (P.cover x) := by
      rw [← hG (hmem x.property)]
      exact hi.localInverse_isLocalDiffeomorphAt
    have hc := hxP.comp (𝓡 3) U hinv
    apply hc.congr_of_eventuallyEq
    have hxsource : P.cover x ∈ hi.localInverse.source := by
      rw [← hG (hmem x.property)]
      exact hi.localInverse_mem_source
    have hev : ∀ᶠ y in 𝓝 (x : UnitThreeSphere),
        P.cover y ∈ hi.localInverse.source :=
      hxP.contMDiffAt.continuousAt (hi.localInverse_open_source.mem_nhds hxsource)
    have heu : ∀ᶠ y in 𝓝 (x : UnitThreeSphere), P.cover y ∈ (U : Set M) :=
      hxP.contMDiffAt.continuousAt (U.isOpen.mem_nhds (hmem x.property))
    filter_upwards [hev, heu] with y hy hyU
    apply Subtype.ext
    rw [hG hyU]
    exact (hi.localInverse_right_inv hy).symm

theorem standardPuncturedProjectiveCover_nonempty_postcompose_diffeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {p : PoincareConjecture.RealProjectiveThree} {V : Set M}
    (P : PoincareConjecture.StandardPuncturedProjectiveCover M p V)
    (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) :
    Nonempty (PoincareConjecture.StandardPuncturedProjectiveCover
      N p ((F : M → N) '' V)) := by
  refine ⟨{
    cover := F ∘ P.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := ?_ }⟩
  · rw [image_comp, P.image_eq]
  · intro x y hx hy
    exact F.injective.eq_iff.trans (P.fibers x y hx hy)
  · intro x
    exact (P.local_diffeomorph x).comp (𝓡 3) N
      (F.isLocalDiffeomorph (P.cover x))

end PoincareConjecture.M25.Topology3D
