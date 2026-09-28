import PoincareConjecture.Proofs.M34.Standard.NonnegativeRicciMetric
import PoincareConjecture.Proofs.M34.Standard.CalibratedMetricComparison
import PoincareConjecture.Proofs.M34.Lemma12_6_Curvature.Nonnegative
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M09.RiemannianProper

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M34

theorem partialFlow_edist_le_initial {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {t : ℝ} (ht : t ∈ Ico 0 F.lifetime)
    (x y : StandardCapSpace) : (F.flow.metric t).edist x y ≤ g0.metric.edist x y := by
  have hnorm (z : StandardCapSpace) (v : TangentSpace (𝓡 3) z) :
      (F.flow.metric t).tangentNorm z v ≤ (1 : ℝ) * g0.metric.tangentNorm z v := by
    have hmono := F.flow.inner_self_antitoneOn_of_nonnegative_ricci
      (convex_Ico 0 F.lifetime) (Subset.refl _) z v (fun s hs =>
        M04.nonneg_ricci_of_nonnegativeSectionalAt (F.flow.connection s) z
          (partialFlow_nonnegativeSectionalCurvature P E0 F s hs z) v)
    have hi := hmono ⟨le_rfl, F.lifetime_pos⟩ ht ht.1
    dsimp only at hi
    rw [F.initial_metric] at hi
    change Real.sqrt ((F.flow.metric t).inner z v v) ≤
      1 * Real.sqrt (g0.metric.inner z v v)
    simpa only [one_mul] using Real.sqrt_le_sqrt hi
  simpa only [ENNReal.ofReal_one, one_mul] using
    edist_le_of_tangentNorm_le g0.metric (F.flow.metric t) zero_lt_one hnorm x y

theorem partialFlow_exists_compact_center_ball_radius {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {X Omega : Set StandardCapSpace}
    (hX : IsCompact X) (hOmega : IsCompact (closure Omega)) :
    ∃ D : ℝ, 0 < D ∧ ∀ t ∈ Ico 0 F.lifetime, ∀ x ∈ X,
      Omega ⊆ (F.flow.metric t).ball x D := by
  let d := Proofs.M09.selectedMetricSpace g0.metric
  have hcont : Continuous (fun z : StandardCapSpace × StandardCapSpace => d.dist z.1 z.2) :=
    @continuous_dist StandardCapSpace d.toPseudoMetricSpace
  obtain ⟨C, hC⟩ := (hX.prod hOmega).exists_bound_of_continuousOn
    hcont.continuousOn
  let D := max C 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hCD : C < D := by dsimp [D]; linarith [le_max_left C 0]
  refine ⟨D, hD, ?_⟩
  intro t ht x hx y hy
  have hd : d.dist x y ≤ C :=
    (le_abs_self _).trans (hC (x, y) ⟨hx, subset_closure hy⟩)
  apply (partialFlow_edist_le_initial F P E0 ht x y).trans_lt
  have hed : g0.metric.edist x y = ENNReal.ofReal (d.dist x y) :=
    @edist_dist StandardCapSpace d.toPseudoMetricSpace x y
  rw [hed]
  exact (ENNReal.ofReal_lt_ofReal_iff hD).mpr (hd.trans_lt hCD)

end PoincareConjecture.M34
