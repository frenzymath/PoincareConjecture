import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteC2AnnulusMotion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FinitePeriodicFirstVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RelabelAreaRange





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}






theorem m64C2Annulus_exists_finite_first_variation
    (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (hsigma0 : ContDiff ℝ 1 sigma0.map) (hsigma1 : ContDiff ℝ 1 sigma1.map)
    (A : M64Annulus (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hstrip : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map
      {p : LoopPlane | p 1 ∈ Ioo (0 : ℝ) 1})
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (F.metric t) (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
      m60AreaGram (F.metric t) A.map p 0 1 = 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ s ∈ Ioo (-epsilon) epsilon, t + s ∈ Ioo a b) ∧
      ∃ v : ℝ → LoopPlane → M,
        (∀ p, v 0 p = A.map p) ∧
        (∀ s x y, v s (annulusPoint (x + curvePeriod) y) = v s (annulusPoint x y)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ x,
          v s (annulusPoint x 0) = c0 (sigma0.map x) (t + s)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ x,
          v s (annulusPoint x 1) = c1 (sigma1.map x) (t + s)) ∧
        (∀ x, curveVelocity (n := n) (fun s => v s (annulusPoint x 0)) 0 =
          m62CurvatureVector F c0 t (sigma0.map x)) ∧
        (∀ x, curveVelocity (n := n) (fun s => v s (annulusPoint x 1)) 0 =
          m62CurvatureVector F c1 t (sigma1.map x)) ∧
        (∀ s ∈ Ioo (-epsilon) epsilon, ∀ g' : RiemannianMetric n M,
          ∃ B : M64Annulus g' ((fun x => c0 x (t + s)) ∘ sigma0.map)
              ((fun x => c1 x (t + s)) ∘ sigma1.map),
            EqOn B.map (v s) m64AnnulusDomain ∧ B.area = m64AnnulusArea g' (v s)) ∧
        let R := fun p =>
          r * (F.connection t).ricci (v 0 p)
            (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
            (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
          r⁻¹ * (F.connection t).ricci (v 0 p)
            (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
            (mfderiv (𝓡 2) (𝓡 n) (v 0) p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
            m64ModulusEnergyDensity (F.metric (t + s)) r (v s) p)
          (r⁻¹ * (∫ x in Icc (0 : ℝ) curvePeriod,
            m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 1) -
              m64FiniteAnnulusCurrent (F.metric t) v 1 (annulusPoint x 0)) -
            ∫ p in m64AnnulusDomain, R p) 0 := by
  obtain ⟨epsilon, hepsilon, htime, v, hbase, hperiod, hlower, hupper,
      hvelocity0, hvelocity1, hfamily, -, d, h, hh, O, hO, hmap, Phi, hPhi, hv⟩ :=
    m64C2Annulus_exists_finite_energy_motion F hc0 hc1 ht sigma0 sigma1 hsigma0 hsigma1 A hA
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hmin : A.area = m64LeastAnnulusArea (F.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map) := by
    rw [M64.leastAnnulusArea_comp_lifts_of_C1
      ((hc0.spatial_regular t ht').of_le (by norm_num)) (hc0.periodic t ht')
      ((hc1.spatial_regular t ht').of_le (by norm_num)) (hc1.periodic t ht') sigma0 sigma1]
    exact hminimum
  refine ⟨epsilon, hepsilon, htime, v, hbase, hperiod, hlower, hupper,
    hvelocity0, hvelocity1, hfamily, ?_⟩
  rw [hv] at hbase hperiod ⊢
  exact m64ParameterAnnulus_periodic_first_variation F ht A hr hmin hconformal hstrip
    hepsilon htime hO hPhi hh hmap hbase hperiod

end PoincareConjecture
