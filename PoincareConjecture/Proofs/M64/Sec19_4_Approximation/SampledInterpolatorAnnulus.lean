import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorLipschitz
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledInterpolatorVertical












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m64_sampled_interpolator_annulus
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {r S B zeta : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (H : ℝ × (M × M) → M)
    (hH : ContMDiffOn
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ
        {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}))
    (hprops : ∀ p q : M, g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q)
    {N : ℕ} (hN : 0 < N) (gamma : C1FreeLoopSpace (M := M))
    (polygon : M63GeodesicPolygon g D N)
    (hsampled : M64SampledPolygon gamma polygon)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop gamma x)
        (curveVelocity (periodicFreeLoop gamma) x) ≤ S)
    (hshort : ∀ x : ℝ,
      g.edist (periodicFreeLoop gamma x) (polygon.map x) < ENNReal.ofReal r)
    (hcol0 : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (H (p 1, periodicFreeLoop gamma (p 0), polygon.map (p 0)))
        (mfderiv (𝓡 2) (𝓡 3)
          (fun q : LoopPlane => H (q 1, periodicFreeLoop gamma (q 0),
            polygon.map (q 0))) p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B)
    (hstrict : B * (2 * S * m63CellLength N) * volume.real m64AnnulusDomain < zeta) :
    ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
      M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
        0 ≤ A.area ∧ A.area < zeta := by
  let U : Set (M × M) := {pq | g.edist pq.1 pq.2 < ENNReal.ofReal r}
  let f : LoopPlane → M := fun p =>
    H (p 1, periodicFreeLoop gamma (p 0), polygon.map (p 0))
  have hpair_global : ∀ x : ℝ, (periodicFreeLoop gamma x, polygon.map x) ∈ U := hshort
  have hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (periodicFreeLoop gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U := by
    intro j p hp
    exact m64_cell_side_short_of_polygon_short polygon hshort j hp
  have hgamma := Proofs.M58.contMDiff_periodicFreeLoop gamma
  have hcontinuous : ContinuousOn f m64AnnulusDomain :=
    m64_interpolator_map_continuous polygon hH hgamma.continuous hpair_global f rfl
  have hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s) :=
    m64_interpolator_map_periodic polygon
      (Proofs.M58.periodic_periodicFreeLoop gamma) f rfl
  obtain ⟨L, hLip⟩ := m64_interpolator_rectangle_lipschitz g hN polygon
    (m64_isOpen_short_pair_tube g r) hH hgamma hpair_global
  have hLip' : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal (L : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hLip
  have hcol1 := m64_sampled_interpolator_vertical_column_bound
    g D hS H hH hprops hN gamma polygon hsampled hbound hshort
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  have hlower : ∀ x : ℝ, f (annulusPoint x 0) = periodicFreeLoop gamma x := by
    intro x
    exact (hprops _ _ (hshort x)).1
  have hupper : ∀ x : ℝ, f (annulusPoint x 1) = polygon.map x := by
    intro x
    exact (hprops _ _ (hshort x)).2.1
  have hmdiff : ∀ j : Fin N, ContMDiffOn (𝓡 2) (𝓡 3) 1 f
      {p | m64PolygonCut N j.castSucc ≤ p 0 ∧
        p 0 ≤ m64PolygonCut N j.succ ∧ 0 ≤ p 1 ∧ p 1 ≤ 1} := by
    intro j
    rw [m64PolygonCut_cellSet]
    exact m64_polygon_cell_contMDiffOn polygon hH hgamma.contMDiffOn hpair j
  let side : ∀ x : ℝ, M63MinimizingGeodesicSide g D 1
      (periodicFreeLoop gamma x) (polygon.map x) := fun x =>
    Classical.choose (m64_interpolator_side_of_short_pair g D
      (hshort x) (contMDiffOn_interpolator_slice hH (hpair_global x))
      (hprops (periodicFreeLoop gamma x) (polygon.map x)))
  have hmap : ∀ x s : ℝ, f (annulusPoint x s) = (side x).map s := by
    intro x s
    exact (Classical.choose_spec (m64_interpolator_side_of_short_pair g D
      (hshort x) (contMDiffOn_interpolator_slice hH (hpair_global x))
      (hprops (periodicFreeLoop gamma x) (polygon.map x))) s).symm
  exact m64AnnulusWitness_of_lipschitz_columns g D f hcontinuous hperiodic
    hlower hupper L.coe_nonneg hB hLip' hfinite hcol0 hcol1 hstrict
    hN (m64PolygonCut N) (m64PolygonCut_strictMono hN)
    m64PolygonCut_zero (m64PolygonCut_last hN) hmdiff side hmap

end PoincareConjecture
