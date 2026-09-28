import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPointAnalytic
import PoincareConjecture.Statements.M27KappaAlternatives












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M34



theorem exists_chapter11_analytic_constant (T : RepairedKappaAlternativeTheory.{u}) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {kappa : ℝ}
        (_K : M30AncientKappaIdentification L kappa),
        letI := L.carrier.topologicalSpace
        letI := L.carrier.chartedSpace
        letI := L.carrier.isManifold
        scalarGradientNorm (L.flow.metric 0) (L.flow.connection 0) L.base < A ∧
          |(L.flow.connection 0).laplacian (L.flow.connection 0).scalarCurvature L.base +
            2 * (L.flow.connection 0).ricciNormSq L.base| < A := by
  obtain ⟨epsilon, hepsilon, htheory⟩ := T.theorem_9_93
  obtain ⟨A, hA, hbound⟩ := htheory (epsilon / 2) (half_pos hepsilon)
    (half_lt_self hepsilon)
  refine ⟨A, hA, ?_⟩
  intro L kappa K
  let := L.carrier.topologicalSpace
  let := L.carrier.measurableSpace
  let := L.carrier.borelSpace
  let := L.carrier.chartedSpace
  let := L.carrier.isManifold
  let := L.carrier.t2Space
  let := L.carrier.t3Space
  let := L.carrier.secondCountable
  let := L.connectedSpace
  let S := K.certificate.solution
  obtain ⟨B, _, hBA, hB⟩ := (hbound S).derivatives
  have hpair : (⟨S.flow.metric 0, S.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g) =
      ⟨L.flow.metric 0, L.flow.connection 0⟩ :=
    Sigma.ext (K.certificate.metric_eq 0 le_rfl) (K.connection_eq 0 le_rfl)
  have hscalar := congrArg (fun gd :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      gd.2.scalarCurvature L.base) hpair
  have hgradient := congrArg (fun gd :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      scalarGradientNorm gd.1 gd.2 L.base) hpair
  have hevolution := congrArg (fun gd :
      Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      gd.2.laplacian gd.2.scalarCurvature L.base + 2 * gd.2.ricciNormSq L.base) hpair
  change (S.flow.connection 0).scalarCurvature L.base =
    (L.flow.connection 0).scalarCurvature L.base at hscalar
  rw [L.scalar_normalized] at hscalar
  obtain ⟨_, hg, d, hd, hdb⟩ := hB 0 le_rfl L.base
  have hdactual := S.flow.hasDerivWithinAt_scalarCurvature 0 self_mem_Iic L.base
  have hdeq := (uniqueDiffOn_Iic (0 : ℝ) 0 self_mem_Iic).eq_deriv _ hd hdactual
  change scalarGradientNorm (S.flow.metric 0) (S.flow.connection 0) L.base =
    scalarGradientNorm (L.flow.metric 0) (L.flow.connection 0) L.base at hgradient
  change (S.flow.connection 0).laplacian (S.flow.connection 0).scalarCurvature L.base +
    2 * (S.flow.connection 0).ricciNormSq L.base = _ at hevolution
  rw [hgradient, hscalar, Real.one_rpow, mul_one] at hg
  rw [hdeq, hevolution, hscalar, one_pow, mul_one] at hdb
  exact ⟨hg.trans_lt hBA, hdb.trans_lt hBA⟩

end PoincareConjecture.M34
