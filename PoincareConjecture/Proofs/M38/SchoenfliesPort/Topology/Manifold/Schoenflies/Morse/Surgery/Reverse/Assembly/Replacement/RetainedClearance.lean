import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.RetainedCollar







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

private theorem prepared_eq_tube_of_height_projection {y : E3}
    (hy : y ∈ range (fun p => S.D (f p)))
    (hheight : |inner Real v y - c| ≤ 2 * S.a)
    (hproj : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1) :
    ∃ q : S1, S.D (f (S.T (q, inner Real v y - c))) = y := by
  let t := inner Real v y - c
  have ht : t ∈ Icc (-(2 * S.a)) (2 * S.a) := abs_le.mp hheight
  obtain ⟨z, hz, hzy⟩ := hproj
  have hplane : y ∈
      (fun x : Hemisphere.Plane v => (c + t) • v + (S.A x : E3)) '' closedBall 0 1 := by
    refine ⟨z, hz, ?_⟩
    have heq := (Poincare.Geometry.Euclidean.heightCoordinates S.unit_v).apply_symm_apply y
    change inner Real v y • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at heq
    rw [← hzy] at heq
    rw [show c + t = inner Real v y by dsimp [t]; ring]
    exact heq
  obtain ⟨p, ⟨q, rfl⟩, heq⟩ := (S.parallel_disk_intersection t ht) ▸
    (show y ∈ ((fun x : Hemisphere.Plane v => (c + t) • v + (S.A x : E3)) ''
      closedBall 0 1) ∩ range (fun p => S.D (f p)) from ⟨hplane, hy⟩)
  exact ⟨q, heq⟩



theorem not_mem_retainedPlus_of_height_projection {y : E3}
    (hheight : |inner Real v y - c| ≤ 2 * S.a)
    (hproj : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1)
    (hcut : inner Real v y < c + S.a) :
    y ∉ (fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1) := by
  rintro ⟨p, hp, rfl⟩
  obtain ⟨q, heq⟩ := S.prepared_eq_tube_of_height_projection (mem_range_self p) hheight hproj
  have hpoint := S.prepared_embedding.isEmbedding.injective heq
  have hpt : S.T (q, inner Real v (S.D (f p)) - c) ∈ S.ePlus '' closedBall 0 1 :=
    hpoint.symm ▸ hp
  by_cases ht : inner Real v (S.D (f p)) - c ≤ -S.a
  · exact disjoint_left.mp S.retained_disjoint
      (S.tube_mem_retainedMinus q (by
        have hh := (abs_le.mp hheight).1
        linarith [S.a_lt_quarter_ε, S.a_pos]) ht) hpt
  · exact S.tube_not_mem_retainedPlus q ⟨lt_of_not_ge ht, by linarith⟩ hpt


theorem not_mem_retainedMinus_of_height_projection {y : E3}
    (hheight : |inner Real v y - c| ≤ 2 * S.a)
    (hproj : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1)
    (hcut : c - S.a < inner Real v y) :
    y ∉ (fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1) := by
  rintro ⟨p, hp, rfl⟩
  obtain ⟨q, heq⟩ := S.prepared_eq_tube_of_height_projection (mem_range_self p) hheight hproj
  have hpoint := S.prepared_embedding.isEmbedding.injective heq
  have hpt : S.T (q, inner Real v (S.D (f p)) - c) ∈ S.eMinus '' closedBall 0 1 :=
    hpoint.symm ▸ hp
  by_cases ht : S.a ≤ inner Real v (S.D (f p)) - c
  · exact disjoint_left.mp S.retained_disjoint hpt
      (S.tube_mem_retainedPlus q (by
        have hh := (abs_le.mp hheight).2
        linarith [S.a_lt_quarter_ε, S.a_pos]) ht)
  · exact S.tube_not_mem_retainedMinus q ⟨by linarith, lt_of_not_ge ht⟩ hpt

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
