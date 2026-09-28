import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.NearlyConformalEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DomainBoundary












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem M64AnnulusNearlyConformalSequenceCertificate.energy_tendsto_infimum
    {S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)}
    (E : M64AnnulusNearlyConformalSequenceCertificate S) :
    Tendsto (fun k => ∫ p in m64AnnulusDomain,
      m60EnergyDensity g (S.sequence k).map p) atTop
        (𝓝 (m64LeastAnnulusArea g c0 c1)) := by
  have herr : Tendsto (fun k =>
      3 * E.conformality_error k * volume.real m64AnnulusDomain)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (E.conformality_error_tendsto.const_mul 3).mul_const
        (volume.real m64AnnulusDomain)
  have hupper : Tendsto (fun k => (S.sequence k).area +
      3 * E.conformality_error k * volume.real m64AnnulusDomain)
      atTop (𝓝 (m64LeastAnnulusArea g c0 c1)) := by
    simpa only [add_zero] using S.area_tendsto_infimum.add herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    S.area_tendsto_infimum hupper
  · intro k
    exact (S.sequence k).area_le_energy
      m64AnnulusDomain_measurableSet (E.energy_integrable k)
  · intro k
    exact (S.sequence k).energy_le_area_add_of_nearlyConformal
      (E.nearly_conformal k) m64AnnulusDomain_measurableSet
      (E.energy_integrable k) m64AnnulusDomain_boundary_null





structure M64WeakEnergyLowerSemicontinuityCertificate
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (C : M64CourantLebesgueArzelaCertificate S)
    (A : M64Annulus g c0 c1) : Prop where
  map_eq_limit : A.map = C.limit.map
  classical_energy_integrable : IntegrableOn (m60EnergyDensity g A.map)
    m64AnnulusDomain volume
  energy_identification :
    (∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p) =
      ∫ p in m64AnnulusDomain,
        m64AnnulusWeakEnergyDensity g C.limit.gradient p
  weak_energy_le_liminf :
    (∫ p in m64AnnulusDomain,
      m64AnnulusWeakEnergyDensity g C.limit.gradient p) ≤
        liminf (fun k => ∫ p in m64AnnulusDomain,
          m60EnergyDensity g (S.sequence (C.subsequence k)).map p) atTop





theorem M64WeakEnergyLowerSemicontinuityCertificate.area_le_infimum
    {S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)}
    {C : M64CourantLebesgueArzelaCertificate S}
    {A : M64Annulus g c0 c1}
    (L : M64WeakEnergyLowerSemicontinuityCertificate S C A) :
    A.area ≤ m64LeastAnnulusArea g c0 c1 := by
  have henergy := C.normalization.energy_tendsto_infimum.comp
    C.subsequence_strictMono.tendsto_atTop
  calc
    A.area ≤ ∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p :=
      A.area_le_energy m64AnnulusDomain_measurableSet
        L.classical_energy_integrable
    _ = ∫ p in m64AnnulusDomain,
        m64AnnulusWeakEnergyDensity g C.limit.gradient p :=
      L.energy_identification
    _ ≤ liminf (fun k => ∫ p in m64AnnulusDomain,
        m60EnergyDensity g (S.sequence (C.subsequence k)).map p) atTop :=
      L.weak_energy_le_liminf
    _ = m64LeastAnnulusArea g c0 c1 := henergy.liminf_eq





theorem M64WeakEnergyLowerSemicontinuityCertificate.toAreaCertificate
    {S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)}
    {C : M64CourantLebesgueArzelaCertificate S}
    {A : M64Annulus g c0 c1}
    (L : M64WeakEnergyLowerSemicontinuityCertificate S C A) :
    M64MorreyLowerSemicontinuityCertificate S C A := by
  refine ⟨L.map_eq_limit, ?_⟩
  have hsub := S.area_tendsto_infimum.comp
    C.subsequence_strictMono.tendsto_atTop
  have hsub' : Tendsto (fun k => (S.sequence (C.subsequence k)).area)
      atTop (𝓝 (m64LeastAnnulusArea g c0 c1)) := by
    simpa only [Function.comp_def] using hsub
  rw [hsub'.liminf_eq]
  exact L.area_le_infimum





noncomputable def m64DouglasMorreyAttainmentCertificate_of_energy_pipeline
    [T3Space M] [PreconnectedSpace M]
    (S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (C : M64CourantLebesgueArzelaCertificate S)
    (H : M64HeinzHildebrandtBoundaryCertificate
      (g := g) (c0 := c0) (c1 := c1) C.limit)
    (L : M64WeakEnergyLowerSemicontinuityCertificate S C
      (m64Annulus_of_heinzHildebrandt (c0 := c0) (c1 := c1) C.limit H)) :
    M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1) :=
  m64DouglasMorreyAttainmentCertificate_of_pipeline S C H
    L.toAreaCertificate

end PoincareConjecture
