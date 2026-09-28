import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap




theorem tendsto_iteratedFDeriv_scalarCurvature_of_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (h : ∀ r : ℕ, r ≤ 2 + m →
      Tendsto (fun a => iteratedFDeriv ℝ r (gseq a).euclideanCoefficients x) l
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x))) :
    Tendsto (fun a => iteratedFDeriv ℝ m (Dseq a).scalarCurvature x) l
      (𝓝 (iteratedFDeriv ℝ m D.scalarCurvature x)) := by
  have hjet : Tendsto
      (fun a => spatialJet (2 + m)
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (gseq a).euclideanCoefficients z.2) (0, x)) l
      (𝓝 (spatialJet (2 + m)
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact h j (by omega)
  have hcont := ((contDiffOn_scalarJetOperator n m).contDiffAt
    ((isOpen_curvatureJetDomain n m).mem_nhds
      (metric_spatialJet_mem_curvatureJetDomain g m x))).continuousAt
  have ht := hcont.tendsto.comp hjet
  rw [scalarJetOperator_spatialJet D] at ht
  exact ht.congr (fun a => scalarJetOperator_spatialJet (Dseq a) m x)

end PoincareConjecture.LeviCivitaData
