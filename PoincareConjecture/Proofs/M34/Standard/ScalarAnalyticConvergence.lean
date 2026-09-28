import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionJet
import PoincareConjecture.Proofs.M34.Standard.ScalarDifferentialJet











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap



theorem tendsto_scalarGradient_tangentNorm_of_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ∀ r : ℕ, r ≤ 3 →
      Tendsto (fun a => iteratedFDeriv ℝ r (gseq a).euclideanCoefficients x) l
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x))) :
    Tendsto (fun a => (gseq a).tangentNorm x
      ((Dseq a).gradient (Dseq a).scalarCurvature x)) l
      (𝓝 (g.tangentNorm x (D.gradient D.scalarCurvature x))) := by
  have hjet : Tendsto
      (fun a => spatialJet 3
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (gseq a).euclideanCoefficients z.2) (0, x)) l
      (𝓝 (spatialJet 3
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact h j (by omega)
  have hcont := (continuousOn_scalarDifferentialNormJet n).continuousAt
    ((isOpen_curvatureJetDomain n 1).mem_nhds
      (metric_spatialJet_mem_curvatureJetDomain g 1 x))
  have ht := hcont.tendsto.comp hjet
  rw [scalarDifferentialNormJet_spatialJet D] at ht
  exact ht.congr (fun a => scalarDifferentialNormJet_spatialJet (Dseq a) x)



theorem tendsto_scalarEvolution_of_metric_jets
    {n : ℕ} {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    (h : ∀ r : ℕ, r ≤ 4 →
      Tendsto (fun a => iteratedFDeriv ℝ r (gseq a).euclideanCoefficients x) l
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients x))) :
    Tendsto (fun a => (Dseq a).laplacian (Dseq a).scalarCurvature x +
      2 * (Dseq a).ricciNormSq x) l
      (𝓝 (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x)) := by
  have hjet : Tendsto
      (fun a => spatialJet 4
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (gseq a).euclideanCoefficients z.2) (0, x)) l
      (𝓝 (spatialJet 4
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients z.2) (0, x))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact h j (by omega)
  have hcont := (continuousOn_scalarEvolutionJet n).continuousAt
    ((isOpen_curvatureJetDomain n 2).mem_nhds
      (metric_spatialJet_mem_curvatureJetDomain g 2 x))
  have ht := hcont.tendsto.comp hjet
  rw [scalarEvolutionJet_spatialJet D] at ht
  exact ht.congr (fun a => scalarEvolutionJet_spatialJet (Dseq a) x)

end PoincareConjecture.LeviCivitaData
