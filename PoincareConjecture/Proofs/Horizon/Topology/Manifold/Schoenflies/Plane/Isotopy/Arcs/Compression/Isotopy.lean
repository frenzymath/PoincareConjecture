import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.Sweep
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.Family

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem exists_marked_disk_compression_family_away_arc
    (b : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (g : E1 → S1) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E1) 1,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x)
    (W O : Set E2) (hW : IsOpen W) (hO : IsOpen O)
    (hDW : (fun x => b (g x)) '' closedBall (0 : E1) 1 ⊆ W)
    (hBO : (b '' closedBall (0 : E2) 1) \
      ((fun x => b (g x)) '' closedBall (0 : E1) 1) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => b (g x)) '' closedBall (0 : E1) 1) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        Phi 1 '' (b '' closedBall (0 : E2) 1) ⊆
          (b '' closedBall (0 : E2) 1) ∩ W := by
  obtain ⟨C, e, hslab, _, _, hzero, hedge⟩ :=
    exists_marked_disk_sweep b g hgi hgl
  exact exists_slab_compression_family_with_relative_support C e
    ((isCompact_closedBall 0 1).image b.continuous) hW hO hslab hzero
    (hedge.trans (image_mono sphere_subset_closedBall)) hDW hBO

theorem exists_supported_disk_isotopy_of_fixed_arc_neighborhood
    (B D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (m : E1 → S1) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E1) 1,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ m x)
    {W O : Set E2} (hW : IsOpen W) (hO : IsOpen O)
    (hmarked : (fun x => B (m x : E2)) '' closedBall (0 : E1) 1 ⊆ W)
    (hDW : ∀ y ∈ W, D y = y)
    (hBO : (B '' closedBall (0 : E2) 1) \
      ((fun x => B (m x : E2)) '' closedBall (0 : E1) 1) ⊆ O)
    (hDBO : (D '' (B '' closedBall (0 : E2) 1)) \
      ((fun x => B (m x : E2)) '' closedBall (0 : E1) 1) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => B (m x : E2)) '' closedBall (0 : E1) 1) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ y, Phi 0 y = y) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t y, y ∉ K → Phi t y = y) ∧
        ∀ y ∈ B '' closedBall (0 : E2) 1, Phi 1 y = D y := by
  obtain ⟨J, hJ, hJO, hJarc, G, hG0, hGs, hGi, hGfix, hGsmall⟩ :=
    exists_marked_disk_compression_family_away_arc B m hmi hml W (O ∩ D ⁻¹' O) hW
      (hO.inter (hO.preimage D.continuous)) hmarked
      (fun y hy => ⟨hBO hy, hDBO ⟨mem_image_of_mem D hy.1, by
        intro hDy
        have hfix := hDW (D y) (hmarked hDy)
        have heq : D y = y := D.injective hfix
        exact hy.2 (heq ▸ hDy)⟩⟩)
  let K := J ∪ D '' J
  have hK : IsCompact K := hJ.union (hJ.image D.continuous)
  have hKO : K ⊆ O := by
    rintro y (hy | ⟨z, hz, rfl⟩)
    · exact (hJO hy).1
    · exact (hJO hz).2
  have hKarc : Disjoint K ((fun x => B (m x : E2)) '' closedBall (0 : E1) 1) := by
    apply disjoint_left.mpr
    rintro y (hy | ⟨z, hz, he⟩) harc
    · exact disjoint_left.mp hJarc hy harc
    · have hzy : z = y := D.injective (he.trans (hDW y (hmarked harc)).symm)
      exact disjoint_left.mp hJarc (hzy ▸ hz) harc
  let Phi (t : Real) := (((G t).trans D.symm).trans (G t).symm).trans D
  have hPhi (t : Real) (y : E2) : Phi t y = D ((G t).symm (D.symm (G t y))) := rfl
  have hGsymmfix (t : Real) (y : E2) (hy : y ∉ J) : (G t).symm y = y := by
    apply (G t).injective
    change G t ((G t).symm y) = G t y
    rw [(G t).apply_symm_apply, hGfix t y hy]
  have hGsymm0 (y : E2) : (G 0).symm y = y := by
    apply (G 0).injective
    change G 0 ((G 0).symm y) = G 0 y
    rw [(G 0).apply_symm_apply, hG0]
  have hPhi0 (y : E2) : Phi 0 y = y := by
    rw [hPhi, hG0, hGsymm0, D.apply_symm_apply]
  have hPhis : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) :=
    D.contDiff.comp (hGi.comp (contDiff_fst.prodMk (D.symm.contDiff.comp hGs)))
  have hPhii : ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) :=
    hGi.comp (contDiff_fst.prodMk (D.contDiff.comp
      (hGs.comp (contDiff_fst.prodMk (D.symm.contDiff.comp contDiff_snd)))))
  refine ⟨K, hK, hKO, hKarc, Phi, hPhi0, hPhis, hPhii, ?_, ?_⟩
  · intro t y hy
    have hyJ : y ∉ J := fun h => hy (Or.inl h)
    have hDyJ : D.symm y ∉ J := fun h =>
      hy (Or.inr ⟨D.symm y, h, D.apply_symm_apply y⟩)
    rw [hPhi, hGfix t y hyJ, hGsymmfix t _ hDyJ, D.apply_symm_apply]
  · intro y hy
    have hGy : G 1 y ∈ W := (hGsmall (mem_image_of_mem (G 1) hy)).2
    have hDinv : D.symm (G 1 y) = G 1 y := by
      apply D.injective
      change D (D.symm (G 1 y)) = D (G 1 y)
      rw [D.apply_symm_apply, hDW _ hGy]
    rw [hPhi, hDinv, (G 1).symm_apply_apply]

end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
