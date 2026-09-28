import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalProtectedRestart
import PoincareConjecture.Proofs.M25.AppA_21_Local.ProtectedForwardExhaustion
import PoincareConjecture.Proofs.M25.AppA_21_Local.LocalNegativeReturnCircle
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SingletonTube









set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture



theorem NeckOnlyCover.exists_finite_chain_or_circle_of_negative_end_avoidance :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ P ∈ H.necks, P.IsNonseparating) →
      ∀ (N : EpsilonNeck g), N.epsilon = H.epsilon → N.center ∈ H.X →
      Disjoint H.X
        (N.region (-H.epsilon⁻¹) (-(4 * H.epsilon⁻¹ / 5))) →
      (∃ (D : BalancedNeckChain g H.epsilon) (a b : ℤ),
        D.shape = ChainShape.finite a b ∧
          H.X ⊆ ⋃ i ∈ D.shape.active, (D.neck i).carrier) ∨
      (∃ F : SphereBundleCircleCertificate g H.X, F.epsilon = H.epsilon) := by
  obtain ⟨er, hrp, hrcap, restart⟩ :=
    NeckOnlyCover.exists_local_restart_with_protected_negative_end.{u}
  obtain ⟨ef, hfp, _, forward⟩ :=
    NeckOnlyCover.exists_finite_forward_chain_or_protected_deep_return.{u}
  obtain ⟨ec, hcp, _, circle⟩ :=
    NeckOnlyCover.exists_circle_certificate_of_local_negative_return.{u}
  refine ⟨min er (min ef ec), by positivity, (min_le_left _ _).trans hrcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hnon N heN hNX havoid
  classical
  rcases le_min_iff.mp he with ⟨her, he⟩
  rcases le_min_iff.mp he with ⟨hef, hec⟩
  have singleton (A : EpsilonNeck g) (epsilon : ℝ) (heA : A.epsilon = epsilon)
      (hcov : H.X ⊆ A.carrier) :
      ∃ (D : BalancedNeckChain g epsilon) (a b : ℤ),
        D.shape = ChainShape.finite a b ∧
          H.X ⊆ ⋃ i ∈ D.shape.active, (D.neck i).carrier := by
    subst epsilon
    refine ⟨A.singletonChain, 0, 0, rfl, ?_⟩
    intro x hx
    exact mem_iUnion₂.mpr ⟨0, ⟨le_rfl, le_rfl⟩, hcov hx⟩
  by_cases hcovered : H.X ⊆ N.carrier
  · exact Or.inl (singleton N H.epsilon heN hcovered)
  obtain ⟨P, Q, hP, hQP, heQ, hQX, hprotected, _hretain, halternative⟩ :=
    restart H her N heN hNX hcovered havoid
  rcases halternative with hcoveredQ | ⟨S, hS, hScenter⟩
  · exact Or.inl (singleton Q H.epsilon heQ hcoveredQ)
  have hQnon : Q.IsNonseparating := by
    rcases hQP with hQP | hQP
    · rw [hQP]
      exact hnon P hP
    · rw [hQP]
      change P.IsNonseparating
      exact hnon P hP
  have hselected : ∃ A ∈ H.necks, Q.SameUpToReversal A := by
    refine ⟨P, hP, ?_⟩
    rcases hQP with hQP | hQP
    · rw [hQP]
      exact P.sameUpToReversal_refl
    · rw [hQP]
      refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
      intro z _
      change P.coordinate_map (z.1, -z.2) = P.coordinate_map (z.1, -1 * z.2)
      rw [neg_one_mul]
  obtain ⟨b, D, _hb, hshape, _hsource, hstart, _hcenters,
    _hquarters, _hhistory, hfinal⟩ :=
    forward H hef Q hselected heQ hQX hQnon hprotected
  rcases hfinal with hcov | ⟨R, _hR, heR, _hRX, hfront, hout, hreturn⟩
  · exact Or.inl ⟨D, 0, b, hshape, hcov⟩
  obtain ⟨_Q', F, _hQ'S, hFeps, _hFcarrier⟩ :=
    circle H hec D 0 b hshape R heR hfront hout
      (by simpa only [hstart] using hreturn) S hS
      (by simpa only [hstart] using hScenter)
  exact Or.inr ⟨F, hFeps⟩

end PoincareConjecture
