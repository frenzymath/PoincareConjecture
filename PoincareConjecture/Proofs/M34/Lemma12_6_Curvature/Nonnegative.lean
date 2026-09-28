import PoincareConjecture.Proofs.M34.Standard.ProperSectionalComparison
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.EndExhaustionLaplacian










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34



theorem partialFlow_nonnegativeSectionalCurvature (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) :
    ∀ t ∈ Ico 0 F.lifetime, (F.flow.connection t).NonnegativeSectionalCurvature := by
  have hpair : (⟨F.flow.metric 0, F.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
        ⟨g0.metric, g0.connection⟩ :=
    Sigma.mk.inj_iff.mpr ⟨F.initial_metric, F.initial_connection⟩
  have hinit : (F.flow.connection 0).NonnegativeSectionalCurvature := by
    have heq := congrArg (fun p : Σ g : RiemannianMetric 3 StandardCapSpace,
      LeviCivitaData g => p.2.NonnegativeSectionalCurvature) hpair
    exact heq.mpr g0.nonnegative_sectional
  intro t ht
  let T := (t + F.lifetime) / 2
  have hT : 0 < T := by dsimp [T]; linarith [F.lifetime_pos, ht.1]
  have htT : t ≤ T := by dsimp [T]; linarith [ht.2]
  have hTF : T < F.lifetime := by dsimp [T]; linarith [ht.2]
  have hsub : Icc 0 T ⊆ Ico 0 F.lifetime :=
    fun _ hs => ⟨hs.1, hs.2.trans_lt hTF⟩
  have hne : (Icc 0 T).Nontrivial :=
    ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, ne_of_lt hT⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F.flow hsub ordConnected_Icc hne
  obtain ⟨B, hB, hfull⟩ := F.curvature_locally_bounded T hT.le hTF
  obtain ⟨C, hC, hlap⟩ := partialFlow_exhaustion_laplacian_bound P E0 F hT.le hTF
  have hresult := nonnegativeSectionalCurvature_of_proper_barrier hT hB hC G
    (fun s hs x => (le_abs_self _).trans (hfull s hs x)) hinit
    (endExhaustion g0.cylindrical_end) (endExhaustion_contMDiff _)
    (one_le_endExhaustion _) (endExhaustion_sublevel_isCompact _)
    (fun s hs x => ((le_abs_self _).trans (hlap s hs x)).trans
      (le_mul_of_one_le_right hC (one_le_endExhaustion _ x)))
  exact hresult t ⟨ht.1, htT⟩

end PoincareConjecture.M34
