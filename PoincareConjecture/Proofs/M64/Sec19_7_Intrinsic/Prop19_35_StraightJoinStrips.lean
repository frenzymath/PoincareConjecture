import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedArcStrips











noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_exists_straight_join_strips
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A B c eta : ℝ} (heta : 0 < eta) (hc : 0 < c)
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A) :
    let w := quarterTurn (deriv alpha A)
    ∃ epsilon > 0, epsilon < eta ∧
      InjOn alpha (Icc (A - epsilon) A) ∧ InjOn beta (Icc B (B + epsilon)) ∧
      ∃ (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G H : OpenPartialHomeomorph ℝ ℝ) (f g : ℝ → ℝ)
        (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
        (P : TransverseGraphCuts f (G (A - epsilon)) (G A)
          (L w).1 (L w).2 (L w).1 (L w).2)
        (Q : TransverseGraphCuts g (H B) (H (B + epsilon))
          (R w).1 (R w).2 (R w).1 (R w).2),
        let S := P.linearCoordinates L.symm G.open_target hf
        let T := Q.linearCoordinates R.symm H.open_target hg
        ∃ delta > 0, delta ≤ P.radius ∧ delta ≤ Q.radius ∧
          (Icc (A - epsilon) A ⊆ G.source ∧ StrictMonoOn G G.source ∧
            ContDiffOn ℝ ∞ G G.source ∧
            (∀ t ∈ G.source, L (alpha t) = (G t, f (G t))) ∧
            G '' Icc (A - epsilon) A = Icc (G (A - epsilon)) (G A) ∧
            Icc (G (A - epsilon)) (G A) ⊆ G.target) ∧
          (Icc B (B + epsilon) ⊆ H.source ∧ StrictMonoOn H H.source ∧
            ContDiffOn ℝ ∞ H H.source ∧
            (∀ t ∈ H.source, R (beta t) = (H t, g (H t))) ∧
            H '' Icc B (B + epsilon) = Icc (H B) (H (B + epsilon)) ∧
            Icc (H B) (H (B + epsilon)) ⊆ H.target) ∧
          ((fun t => S (t, 0)) '' Icc (0 : ℝ) 1 = alpha '' Icc (A - epsilon) A) ∧
          ((fun t => T (t, 0)) '' Icc (0 : ℝ) 1 = beta '' Icc B (B + epsilon)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
            ∀ z y : ℝ, |z| < delta → |y| < delta →
              (t, z) ∈ S.source ∧ (s, y) ∈ T.source ∧
                (S (t, z) = T (s, y) → t = 1 ∧ s = 0)) ∧
          ∀ h k : ℝ → ℝ,
            (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t ∧ h t < delta) →
            (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t < delta) →
            ∀ r : ℝ, 0 ≤ r → r ∈ P.right.parameter.source → r ∈ Q.left.parameter.source →
              h 1 = P.right.parameter r → k 0 = Q.left.parameter r →
              S '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
                T '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ k q.1} =
                  segment ℝ (alpha A) (alpha A + r • w) := by
  obtain ⟨epsilon, hepsilon, heeta, hleft, hright, hai, hbi, hmeet⟩ :=
    m64Intrinsic_straight_join_local_geometry ha hb heta hc hend hreg htan
  refine ⟨epsilon, hepsilon, heeta, hai, hbi, ?_⟩
  exact m64Intrinsic_exists_joined_arc_strips ha hb
    (by linarith : A - epsilon < A) (by linarith : B < B + epsilon)
    (deriv alpha A) (quarterTurn (deriv alpha A))
    (fun t ht => (hleft t ht).1) (fun t ht => (hright t ht).1)
    (fun t ht => (hleft t ht).2) (fun t ht => (hright t ht).2) hend hmeet

end PoincareConjecture
