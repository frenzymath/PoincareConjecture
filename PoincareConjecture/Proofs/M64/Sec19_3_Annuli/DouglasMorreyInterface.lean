import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimizingSequence













set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}








structure M64DouglasMorreyAttainmentCertificate where
  sequence : ℕ → M64Annulus g c0 c1
  sequence_antitone : Antitone (fun k => (sequence k).area)
  sequence_tendsto_infimum :
    Tendsto (fun k => (sequence k).area) atTop
      (𝓝 (m64LeastAnnulusArea g c0 c1))
  limit : M64Annulus g c0 c1
  sequence_tendsto_limit : ∀ p ∈ m64AnnulusDomain,
    Tendsto (fun k => (sequence k).map p) atTop (𝓝 (limit.map p))
  limit_area_le : limit.area ≤ m64LeastAnnulusArea g c0 c1





theorem M64DouglasMorreyAttainmentCertificate.limit_area_eq_infimum
    (C : M64DouglasMorreyAttainmentCertificate (g := g) (c0 := c0) (c1 := c1)) :
    C.limit.area = m64LeastAnnulusArea g c0 c1 := by
  exact le_antisymm C.limit_area_le
    (m64LeastAnnulusArea_le_annulus C.limit)







noncomputable def m64DouglasMorreyAttainmentCertificate_of_limit
    (seed : M64Annulus g c0 c1) (limit : M64Annulus g c0 c1)
    (hpointwise : ∀ p ∈ m64AnnulusDomain,
      Tendsto (fun k => (Classical.choose
        (m64Annulus_exists_minimizing_sequence seed) k).map p) atTop
        (𝓝 (limit.map p)))
    (hlimit : limit.area ≤ m64LeastAnnulusArea g c0 c1) :
    M64DouglasMorreyAttainmentCertificate (g := g) (c0 := c0) (c1 := c1) :=
  let witness := Classical.choose (m64Annulus_exists_minimizing_sequence seed)
  let properties := Classical.choose_spec (m64Annulus_exists_minimizing_sequence seed)
  { sequence := witness
    sequence_antitone := properties.1
    sequence_tendsto_infimum := properties.2
    limit := limit
    sequence_tendsto_limit := hpointwise
    limit_area_le := hlimit }






noncomputable def m64AnnulusBranchSet
    (A : M64Annulus g c0 c1) : Set LoopPlane :=
  {p | p ∈ interior m64AnnulusDomain ∧
    mfderiv (𝓡 2) (𝓡 n) A.map p = 0}








def M64AnnulusAreaStationary
    (A : M64Annulus g c0 c1) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ variation : ℝ × LoopPlane → M,
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ variation
        (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain) →
      (∀ s ∈ Ioo (-epsilon) epsilon,
        ∃ B : M64Annulus g c0 c1, B.map = fun p => variation (s, p)) →
      (∀ p ∈ m64AnnulusDomain, variation (0, p) = A.map p) →
      HasDerivAt
        (fun s => m64AnnulusArea g (fun p => variation (s, p))) 0 0





structure M64AnnulusBranchAwareFirstVariationCertificate
    (A : M64Annulus g c0 c1) : Prop where
  regularity : M64AnnulusRegularityCertificate A
  area_stationary : M64AnnulusAreaStationary A
  finite_branch_set : (m64AnnulusBranchSet A).Finite
  injective_off_branch_set : ∀ p ∈ interior m64AnnulusDomain,
    p ∉ m64AnnulusBranchSet A →
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p)






def m64MinimalAnnulusData_of_douglasMorrey
    (attainment : M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (variation : M64AnnulusBranchAwareFirstVariationCertificate
      attainment.limit) :
    M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1) := by
  exact m64MinimalAnnulusData_of_certificates attainment.limit
    attainment.limit_area_eq_infimum variation.regularity





theorem exists_m64MinimalAnnulus
    (attainment : M64DouglasMorreyAttainmentCertificate
      (g := g) (c0 := c0) (c1 := c1))
    (variation : M64AnnulusBranchAwareFirstVariationCertificate
      attainment.limit) :
    ∃ B : M64Annulus g c0 c1, B.area = m64LeastAnnulusArea g c0 c1 ∧
      M64PiecewiseC1Annulus B ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ B.map (interior m64AnnulusDomain) := by
  refine ⟨attainment.limit, attainment.limit_area_eq_infimum,
    variation.regularity.piecewise_c1, variation.regularity.interior_smooth⟩

end PoincareConjecture
