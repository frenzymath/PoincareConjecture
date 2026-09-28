import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorVerticalColumnAE
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorWitness












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64_interpolator_annulus_witness_of_cell_columns
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {N : ℕ} (hN : 0 < N)
    (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    {r L K1 zeta : ℝ}
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U)
    (hpair_global : ∀ x : ℝ, (gamma x, polygon.map x) ∈ U)
    (hshort : ∀ x : ℝ,
      g.edist (gamma x) (polygon.map x) < ENNReal.ofReal r)
    (hprops : ∀ p q : M, g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
            (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q)
    (f : LoopPlane → M)
    (hf : f = (fun p : LoopPlane =>
      H (p 1, gamma (p 0), polygon.map (p 0))))
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {hL : 0 ≤ L}
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    (hcolumn : ∀ j : Fin N, ∀ z ∈ interior (m64PolygonCellSet j),
      g.tangentNorm
          (H (z 1, gamma (z 0),
            (polygon.side j).map (z 0 - m63CellLeft N j)))
          (mfderiv (𝓡 2) (𝓡 n)
            (fun p : LoopPlane => H (p 1, gamma (p 0),
              (polygon.side j).map (p 0 - m63CellLeft N j))) z
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1)
    (hstrict : (2 * L) * K1 * volume.real m64AnnulusDomain < zeta) :
    ∃ A : M64Annulus g gamma polygon.map,
      M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
        0 ≤ A.area ∧ A.area < zeta := by
  have hcol1 :=
    m64_interpolator_vertical_column_ae_of_cell_extensions
      (g := g) (D := D) hN polygon (gamma := gamma) (H := H)
      (f := f) hf hcolumn
  exact m64_interpolator_annulus_witness_of_columns
    g D hN polygon hH hgamma hpair hpair_global hshort hprops f hf
    hcontinuous hperiodic (hL := hL) hLip hfinite hcol1 hstrict

end PoincareConjecture
