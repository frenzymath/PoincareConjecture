import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.OpenRegion.Points
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.OpenRegion.Shrinking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.Nested



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies



theorem exists_supported_matching_of_balls_in_open_region {n : Nat}
    (A B : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (O : Set (EuclideanSpace Real (Fin n))) (hO : IsOpen O) (hc : IsConnected O)
    (hAO : A '' closedBall 0 1 ⊆ O) (hBO : B '' closedBall 0 1 ⊆ O) :
    ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧ K ⊆ O ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, D x = x) ∧ D '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  let E := EuclideanSpace Real (Fin n)
  have hzero : (0 : E) ∈ closedBall 0 1 := by simp
  have hA0 : A 0 ∈ O := hAO ⟨0, hzero, rfl⟩
  have hB0 : B 0 ∈ O := hBO ⟨0, hzero, rfl⟩
  obtain ⟨KP, hKP, hKPO, P, hPfix, hP0⟩ :=
    exists_supported_point_motion_in_open_region O hO hc.isPreconnected hA0 hB0
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO (B 0) hB0
  let C := ballAffineDiffeomorph (B 0) hr
  have hC : C '' ball 0 1 = ball (B 0) r := ballAffineDiffeomorph_image_ball _ hr
  obtain ⟨KA, hKA, hKAO, SA, hSAfix, hSA⟩ :=
    exists_supported_ball_shrinking_in_open_region A O (P ⁻¹' ball (B 0) r)
      hO (isOpen_ball.preimage P.continuous) hAO (by
        change P (A 0) ∈ ball (B 0) r
        rw [hP0]
        exact mem_ball_self hr)
  obtain ⟨KB, hKB, hKBO, SB, hSBfix, hSB⟩ :=
    exists_supported_ball_shrinking_in_open_region B O (ball (B 0) r)
      hO isOpen_ball hBO (mem_ball_self hr)
  let A' := (A.trans SA).trans P
  let B' := B.trans SB
  have hA' : A' '' closedBall 0 1 ⊆ C '' ball 0 1 := by
    rw [hC]
    rintro _ ⟨x, hx, rfl⟩
    exact hSA ⟨A x, ⟨x, hx, rfl⟩, rfl⟩
  have hB' : B' '' closedBall 0 1 ⊆ C '' ball 0 1 := by
    rw [hC]
    rintro _ ⟨x, hx, rfl⟩
    exact hSB ⟨B x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨KF, hKF, hKFC, F, hFfix, hF⟩ :=
    exists_supported_matching_inside_ball A' B' C hA' hB'
  have hKFO : KF ⊆ O := hKFC.trans (hC.symm ▸ hrO)
  let D := ((SA.trans P).trans F).trans SB.symm
  refine ⟨((KA ∪ KP) ∪ KF) ∪ KB, ((hKA.union hKP).union hKF).union hKB,
    union_subset (union_subset (union_subset hKAO hKPO) hKFO) hKBO, D, ?_, ?_⟩
  · intro x hx
    change SB.symm (F (P (SA x))) = x
    rw [hSAfix x (fun h => hx (Or.inl (Or.inl (Or.inl h)))),
      hPfix x (fun h => hx (Or.inl (Or.inl (Or.inr h)))),
      hFfix x (fun h => hx (Or.inl (Or.inr h)))]
    apply SB.injective
    change SB (SB.symm x) = SB x
    rw [SB.apply_symm_apply, hSBfix x (fun h => hx (Or.inr h))]
  · calc
      D '' (A '' closedBall 0 1) = SB.symm '' (F '' (A' '' closedBall 0 1)) := by
        simp only [image_image]
        rfl
      _ = SB.symm '' (B' '' closedBall 0 1) := by rw [hF]
      _ = B '' closedBall 0 1 := by
        rw [image_image]
        congr 1
        funext x
        exact SB.symm_apply_apply (B x)

end Poincare.Manifold.Schoenflies
