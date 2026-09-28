import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceSuccessorOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}




theorem source_edge_orientations_agree
    {N P Q R T V : EpsilonNeck g} {γ : ℝ → M} {a b tN tQ tR : ℝ}
    (H₀ : SourceEdgeCommonOrientationPacket N P Q (γ := γ) tN tQ)
    (H₁ : SourceEdgeCommonOrientationPacket R T V (γ := γ) tQ tR)
    (hR : R = P ∨ R = P.reversed) (hε : N.epsilon ≤ 1 / 1000)
    {U : Set M} (hNU : N.carrier ⊆ U)
    (haN : a ≤ tN) (hNQ : tN < tQ) (hRb : tR ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b)) : Q = R := by
  have hbad (hcarrier : R.carrier = Q.carrier)
      (haxis : ∀ x, (R.coordinate_inverse x).2 = -(Q.coordinate_inverse x).2) :
      False := by
    obtain ⟨v, hv, hlevel, _, _⟩ := H₁.transition
    have hvQ : γ v ∈ Q.carrier := by
      rw [← hcarrier]
      exact H₁.edge ⟨hv.1.le, hv.2⟩
    have hRε : R.epsilon = N.epsilon := by
      have hp : P.epsilon = N.epsilon := by
        rcases H₀.choice with h | h
        · simpa only [h] using H₀.epsilon_eq
        · simpa only [h, reversed_epsilon] using H₀.epsilon_eq
      rcases hR with h | h <;> simpa only [h, reversed_epsilon] using hp
    have hs := successor_exit_sign_eq_one_of_minimizer N Q hε H₀.epsilon_eq
      (N.carrier_open.frontier_eq ▸ H₀.frontier).2 H₀.reciprocal_region hNU
      haN hNQ hv.1 (hv.2.le.trans hRb) hγ hγU hfinite hmin H₀.center_N
      H₀.center_Q hvQ (Or.inr (rfl : (-1 : ℝ) = -1))
      (by simpa only [neg_one_mul, ← haxis, hRε, H₀.epsilon_eq] using hlevel)
    norm_num at hs
  rcases H₀.choice with hQ | hQ <;> rcases hR with hR | hR
  · exact hQ.trans hR.symm
  · exact False.elim (hbad
      (by simp only [hR, hQ, reversed_carrier])
      (by intro x; simp only [hR, hQ, reversed_coordinate_inverse]))
  · exact False.elim (hbad
      (by simp only [hR, hQ, reversed_carrier])
      (by intro x; simp only [hR, hQ, reversed_coordinate_inverse, neg_neg]))
  · exact hQ.trans hR.symm

end PoincareConjecture.M28
