import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Compression.MarkedBall

/-!
# Localizing a ball equivalence by marked compression

Compress the ball into a fixed neighborhood of its marked disk. Conjugating
that compression by the given equivalence gives the same compressed ball.
The resulting commutator agrees with the equivalence on the entire ball and
has support in the prescribed neighborhood of the two balls.

Reference: Hatcher, Notes on Basic 3-Manifold Topology (2014),
Lemma 1.3 and reverse-surgery induction, printed pp. 4-5.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

/-- A ball equivalence fixing a neighborhood of a marked disk can be
realized with compact support in any open set containing the two filled
balls off that disk. The map agrees on the entire source ball. -/
theorem exists_supported_ball_equivalence_of_fixed_disk_neighborhood
    (B D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (m : E2 → S2) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x)
    {W O : Set E3} (hW : IsOpen W) (hO : IsOpen O)
    (hmarked : (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 ⊆ W)
    (hDW : ∀ y ∈ W, D y = y)
    (hBO : (B '' closedBall (0 : E3) 1) \
      ((fun x => B (m x : E3)) '' closedBall (0 : E2) 1) ⊆ O)
    (hDBO : (D '' (B '' closedBall (0 : E3) 1)) \
      ((fun x => B (m x : E3)) '' closedBall (0 : E2) 1) ⊆ O) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => B (m x : E3)) '' closedBall (0 : E2) 1) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        ∀ y ∈ B '' closedBall (0 : E3) 1, F y = D y := by
  obtain ⟨J, hJ, hJO, hJdisk, G, hGfix, hGsmall⟩ :=
    Rounding.exists_marked_ball_compression_away_disk B m hmi hml W (O ∩ D ⁻¹' O) hW
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
  have hKdisk : Disjoint K ((fun x => B (m x : E3)) '' closedBall (0 : E2) 1) := by
    apply disjoint_left.mpr
    rintro y (hy | ⟨z, hz, he⟩) hdisk
    · exact disjoint_left.mp hJdisk hy hdisk
    · have hzy : z = y := D.injective (he.trans (hDW y (hmarked hdisk)).symm)
      exact disjoint_left.mp hJdisk (hzy ▸ hz) hdisk
  let F := ((G.trans D.symm).trans G.symm).trans D
  have hF (y : E3) : F y = D (G.symm (D.symm (G y))) := rfl
  have hGsymmfix (y : E3) (hy : y ∉ J) : G.symm y = y := by
    apply G.injective
    change G (G.symm y) = G y
    rw [G.apply_symm_apply, hGfix y hy]
  refine ⟨K, hK, hKO, hKdisk, F, ?_, ?_⟩
  · intro y hy
    have hyJ : y ∉ J := fun h => hy (Or.inl h)
    have hDyJ : D.symm y ∉ J := fun h =>
      hy (Or.inr ⟨D.symm y, h, D.apply_symm_apply y⟩)
    rw [hF, hGfix y hyJ, hGsymmfix _ hDyJ, D.apply_symm_apply]
  · intro y hy
    have hGy : G y ∈ W := (hGsmall (mem_image_of_mem G hy)).2
    have hDinv : D.symm (G y) = G y := by
      apply D.injective
      change D (D.symm (G y)) = D (G y)
      rw [D.apply_symm_apply, hDW _ hGy]
    rw [hF, hDinv, G.symm_apply_apply]

end Poincare.Manifold.Schoenflies.Reverse
