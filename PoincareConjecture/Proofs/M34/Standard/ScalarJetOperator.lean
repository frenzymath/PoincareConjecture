import PoincareConjecture.Proofs.M34.Standard.ScalarMetricJets
import PoincareConjecture.Proofs.M34.Standard.CurvatureJetRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

theorem RiemannianMetric.inverseCoefficients_eq_inverse_gram {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    g.inverseCoefficients x i j =
      (Matrix.of (fun a b => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)))⁻¹ i j := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (fun v : TangentSpace (𝓡 n) x => EuclideanSpace.proj j v)
    ((g.orthonormalBasis x).sum_repr' ((g.inner x).inverse (EuclideanSpace.proj i)))
  have hp (k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      inner ℝ (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) =
        EuclideanSpace.proj i (g.orthonormalBasis x k) := by
    change g.inner x (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) = _
    rw [g.symm, (g.inner_isInvertible x).self_apply_inverse]
    rfl
  have hexp : g.inverseCoefficients x i j =
      ∑ k, EuclideanSpace.proj i (g.orthonormalBasis x k) *
        EuclideanSpace.proj j (g.orthonormalBasis x k) := by
    simpa only [OrthonormalBasis.repr_apply_apply, hp, map_sum, map_smul,
      smul_eq_mul, RiemannianMetric.inverseCoefficients] using h.symm
  rw [hexp]
  convert! sum_basis_repr_mul_eq_inverse_gram
      (show Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) from
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) (g.orthonormalBasis x) i j using 1

namespace M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

noncomputable def scalarTwoJet {n : ℕ} (J : MetricTwoJet n) : ℝ :=
  ∑ i, ∑ j, EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i)) *
    jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)

theorem contDiffAt_scalarTwoJet {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ scalarTwoJet J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  unfold scalarTwoJet
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
    (hI.clm_apply contDiffAt_const)).mul (contDiffAt_jetRicci hJ _ _)

theorem scalarTwoJet_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    scalarTwoJet (metricTwoJet g.euclideanCoefficients x) = D.scalarCurvature x := by
  rw [D.scalarCurvature_eq_inverse_gram x (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp only [scalarTwoJet, jetRicci_metricTwoJet D]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact g.inverseCoefficients_eq_inverse_gram x i j

noncomputable def scalarJetOperator (n m : ℕ) :
    Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) (2 + m) →
      (EuclideanSpace ℝ (Fin n)) [×m]→L[ℝ] ℝ :=
  operator 2 (scalarTwoJet ∘ twoJetProjection n) m

theorem contDiffOn_scalarJetOperator (n m : ℕ) :
    ContDiffOn ℝ ∞ (scalarJetOperator n m) (curvatureJetDomain n m) := by
  apply contDiffOn_operator (isOpen_jetRicciFlowDomain n)
  intro J hJ
  exact ((contDiffAt_scalarTwoJet hJ).comp J
    (twoJetProjection n).contDiff.contDiffAt).contDiffWithinAt

theorem scalarJetOperator_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    scalarJetOperator n m
      (spatialJet (2 + m) (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        g.euclideanCoefficients p.2) (0, x)) =
      iteratedFDeriv ℝ m D.scalarCurvature x := by
  have hQ : ContDiffOn ℝ ∞ (scalarTwoJet ∘ twoJetProjection n) (jetRicciFlowDomain n) := by
    intro J hJ
    exact ((contDiffAt_scalarTwoJet hJ).comp J
      (twoJetProjection n).contDiff.contDiffAt).contDiffWithinAt
  have hB : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have h := operator_spatialJet (isOpen_jetRicciFlowDomain n) hQ
    (J := univ) (U := univ) (hB.comp contDiff_snd).contDiffOn isOpen_univ isOpen_univ
    (fun z _ => by
      change ((twoJetProjection n (spatialJet 2
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) z)).1).IsInvertible
      rw [twoJetProjection_spatialJet]
      exact g.inner_isInvertible z.2)
    (t := 0) (mem_univ _) (x := x) (mem_univ _) m
  simp only [Function.comp_apply, twoJetProjection_spatialJet,
    scalarTwoJet_metricTwoJet D] at h
  convert! h using 1

end M34
end PoincareConjecture
