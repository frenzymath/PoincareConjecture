import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.WeightedAreaEnergyRigidity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusAreaStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakClassicalColumns

















set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n m : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem m64FreeObservedWeakAnnulus_minimal_conformal_of_admission
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (L : M64ObservedWeakAnnulus (n := n) e (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hbound : L.weightedEnergy Q r ≤ m64LeastAnnulusArea g c0 c1)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hmap : L.map = A.map)
    (hinterior : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map (interior m64AnnulusDomain)) :
    A.area = m64LeastAnnulusArea g c0 c1 ∧
      m64ClassicalWeightedGramEnergy g A r = A.area ∧
      (∀ᵐ p ∂volume.restrict m64AnnulusDomain,
        r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
          m60AreaGram g A.map p 0 1 = 0) ∧
      M64AnnulusAreaStationary A := by
  have hLinterior : ContMDiffOn (𝓡 2) (𝓡 n) 1 L.map
      (interior m64AnnulusDomain) := by
    simpa only [hmap] using hinterior
  have hcolumns : ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
      L.column i p = fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1) := by
    intro i
    have hi := L.classical_columns_of_contMDiffOn he hLinterior i
    filter_upwards [hi] with p hp
    simpa only [hmap] using hp
  have henergy : L.weightedEnergy Q r = m64ClassicalWeightedGramEnergy g A r :=
    m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he Q hdiag L hmap hcolumns r
  have htransport : M64FreeBoundaryAreaTransport g c0 c1 :=
    m64FreeBoundaryAreaTransport_of_collars hc0.continuous hp0
      (m64PeriodicC1Curve_metric_lipschitz g hc0 hp0) hc1.continuous hp1
      (m64PeriodicC1Curve_metric_lipschitz g hc1 hp1)
  obtain ⟨A0, hA0⟩ := htransport sigma0 sigma1 A
  have hlower : m64LeastAnnulusArea g c0 c1 ≤ A.area :=
    (m64LeastAnnulusArea_le_annulus A0).trans_eq hA0
  have harea : A.area ≤ m64ClassicalWeightedGramEnergy g A r :=
    A.area_le_weightedGramEnergy hr (A.weightedGramEnergy_integrable r)
  have hupper : m64ClassicalWeightedGramEnergy g A r ≤
      m64LeastAnnulusArea g c0 c1 := henergy ▸ hbound
  have hminimum : A.area = m64LeastAnnulusArea g c0 c1 :=
    le_antisymm (harea.trans hupper) hlower
  have heq : m64ClassicalWeightedGramEnergy g A r = A.area :=
    le_antisymm (hupper.trans_eq hminimum.symm) harea
  have hconformal := A.ae_modulus_conformal_of_weightedEnergy_eq_area hr
    (A.weightedGramEnergy_integrable r) heq
  refine ⟨hminimum, heq, hconformal, ?_⟩
  exact m64AnnulusAreaStationary_of_modulus_conformal_minimum A hr
    (m64FreeAnnulus_minimizes_own_boundary htransport sigma0 sigma1 A hminimum)
    hconformal

end PoincareConjecture
