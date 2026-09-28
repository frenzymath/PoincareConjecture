import PoincareConjecture.Proofs.M35.Thm12_28.StrongCanonicalScalar
import PoincareConjecture.Proofs.M35.Thm12_28.StrongFirstFailure
import PoincareConjecture.Proofs.M35.Thm12_28.Nonnegative
import PoincareConjecture.Proofs.M35.Thm12_28.CompactBalls
import PoincareConjecture.Proofs.M35.Thm12_28.NoncollapsedSlabs









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem exists_ancient_extraction_threshold (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ epsilon C : ℝ, 0 < epsilon → epsilon ≤ delta → 0 < C →
        ∀ (g₀ : StandardInitialMetric) (E : RepairedStandardCapExistenceData g₀)
          (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
          (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
          (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k))
            atTop atTop),
          (∀ k, generalizedEarlierStrongCanonicalNeighborhoods
            ((blowupSequence P E t x ht hR).flow k) epsilon C
            ((blowupSequence P E t x ht hR).base k).1
            ((blowupSequence P E t x ht hR).base k).2) →
          ∃ kappa : ℝ, 0 < kappa ∧
            ∃ L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
              (blowupBackwardInterval ⊤),
              Nonempty (M30AncientKappaIdentification L.limit kappa) := by
  obtain ⟨delta, A, hdelta, hA, hbounds⟩ := exists_strong_canonical_scalar_bounds P
  obtain ⟨epsilon₀, hepsilon₀, _, hlimits⟩ := P.long_limits
  refine ⟨min delta epsilon₀, lt_min hdelta hepsilon₀, ?_⟩
  intro epsilon C he hemin hC g₀ E t x ht hR hcanonical
  obtain ⟨N⟩ := E.noncollapsing
  let S := blowupSequence P E t x ht hR
  have hedelta : epsilon ≤ delta := hemin.trans (min_le_left _ _)
  have H : M30LongBlowupControls S epsilon C N.kappa N.radius 1 ⊤ := by
    refine {
      epsilon_pos := he
      C_pos := hC
      kappa_pos := N.kappa_pos
      radius_pos := N.radius_pos
      branch := fun _ => Or.inr (generalized_nonnegative P E)
      canonical := fun k => (hcanonical k).left_dense
      analytic_constant := max A C
      analytic_constant_pos := hA.trans_le (le_max_left _ _)
      scalar_gradient_bound := ?_
      scalar_time_derivative_bound := ?_
      balls_compact := blowupSequence_balls_compact P E t x ht hR
      noncollapsed_at_zero := fun B _ =>
        blowupSequence_noncollapsed_at_zero P E t x ht hR N B
      mu_pos := zero_lt_one
      maximal_worldlines := blowupSequence_worldlines P E t x ht hR zero_le_one
      horizon_pos := ENNReal.zero_lt_top
      slabs := fun T _ _ B _ => blowupSequence_noncollapsed_slabs P E t x ht hR N B T
    }
    · intro k s hs hst y hhigh v hv
      obtain ⟨hgood⟩ := hcanonical k s hs hst y hhigh
      exact (hbounds epsilon C hedelta E.atlas g₀ E.flow s y hgood).1 v hv
    · intro k b s hs hst y hhigh
      have hscalar := scalar_eq P E.flow.base.flow hs y
      have hhigh' : 4 * S.scale k ≤ (generalizedFlow E.flow.base.flow).scalar
          ⟨s, (sliceDiffeomorph hs).symm y⟩ := hhigh.trans_eq hscalar.symm
      obtain ⟨hgood⟩ := hcanonical k s hs hst ((sliceDiffeomorph hs).symm y) hhigh'
      exact ⟨_, P.curvature.scalar_evolution 3 StandardCapSpace _ E.flow.base.flow s hs y,
        (hbounds epsilon C hedelta E.atlas g₀ E.flow s
          ((sliceDiffeomorph hs).symm y) hgood).2⟩
  obtain ⟨L⟩ := hlimits S epsilon C N.kappa N.radius 1 ⊤
    (hemin.trans (min_le_right _ _)) H
  exact ⟨N.kappa, N.kappa_pos, L.convergence, L.ancient rfl⟩

end PoincareConjecture.M35.OrdinaryRealization
