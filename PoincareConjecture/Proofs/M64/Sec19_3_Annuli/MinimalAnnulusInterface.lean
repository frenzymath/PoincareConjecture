import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {c0 c1 : ℝ → M}






structure M64MinimalAnnulusData where
  annulus : M64Annulus g c0 c1
  area_minimal : annulus.area = m64LeastAnnulusArea g c0 c1
  piecewise_c1 : M64PiecewiseC1Annulus annulus
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 n) ∞ annulus.map
    (interior m64AnnulusDomain)




theorem M64MinimalAnnulusData.area_nonneg
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    0 ≤ A.annulus.area :=
  A.annulus.area_nonneg





theorem M64MinimalAnnulusData.area_eq_sInf
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    A.annulus.area = sInf (m64AnnulusAreaRange g c0 c1) :=
  A.area_minimal




theorem M64MinimalAnnulusData.area_le
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1))
    (B : M64Annulus g c0 c1) :
    A.annulus.area ≤ B.area := by
  rw [A.area_minimal]
  exact m64LeastAnnulusArea_le_annulus B




theorem m64MinimalAnnulus_areaRange_nonempty
    (A : M64MinimalAnnulusData (g := g) (c0 := c0) (c1 := c1)) :
    (m64AnnulusAreaRange g c0 c1).Nonempty :=
  m64AnnulusAreaRange_nonempty A.annulus




theorem m64MinimalAnnulus_areaRange_bddBelow
    : BddBelow (m64AnnulusAreaRange g c0 c1) :=
  m64AnnulusAreaRange_bddBelow g c0 c1

end PoincareConjecture
