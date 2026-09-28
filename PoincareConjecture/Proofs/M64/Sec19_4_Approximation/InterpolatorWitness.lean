import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.HorizontalColumn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in

theorem m64_interpolator_side_of_short_pair
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {p q : M} {r : ℝ} {H : ℝ × (M × M) → M}
    (hr : g.edist p q < ENNReal.ofReal r)
    (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n)
      ∞ (fun t : ℝ => H (t, p, q)) (Ioo (-1 : ℝ) 2))
    (hprops : g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
            (fun s => H (s, p, q)) t 1) = (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q) :
    ∃ side : M63MinimizingGeodesicSide g D 1 p q,
      ∀ t : ℝ, side.map t = H (t, p, q) := by
  rcases hprops hr with ⟨h0, h1, hgeo, hspeed, hlength⟩
  let side : M63MinimizingGeodesicSide g D 1 p q := {
    map := fun t => H (t, p, q)
    domain := Ioo (-1 : ℝ) 2
    domain_open := isOpen_Ioo
    interval_subset := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    smooth := hsmooth
    start := h0
    finish := h1
    speed := (g.edist p q).toReal
    speed_nonnegative := ENNReal.toReal_nonneg
    constant_speed := by
      intro t ht
      have hIoo : t ∈ Ioo (-1 : ℝ) 2 := by
        constructor <;> linarith [ht.1, ht.2]
      exact hspeed t hIoo
    equation := by
      intro t ht
      have hIoo : t ∈ Ioo (-1 : ℝ) 2 := by
        constructor <;> linarith [ht.1, ht.2]
      exact hgeo.pullback_velocity_eq_zero D hIoo
    minimizing := hlength }
  refine ⟨side, ?_⟩
  intro t
  rfl

theorem m64_interpolator_annulus_witness_of_columns
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
    (hf : f = (fun p : LoopPlane => H (p 1, gamma (p 0), polygon.map (p 0))))
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {hL : 0 ≤ L}
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    (hcol1 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z
            (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1)
    (hstrict : (2 * L) * K1 * volume.real m64AnnulusDomain < zeta) :
    ∃ A : M64Annulus g gamma polygon.map,
      M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
        0 ≤ A.area ∧ A.area < zeta := by
  have hlower : ∀ x : ℝ,
      f (annulusPoint x 0) = gamma x := by
    intro x
    rw [hf]
    have hp := hprops (gamma x) (polygon.map x) (hshort x)
    simpa only [annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_apply, one_apply] using hp.1
  have hupper : ∀ x : ℝ, f (annulusPoint x 1) = polygon.map x := by
    intro x
    rw [hf]
    have hp := hprops (gamma x) (polygon.map x) (hshort x)
    simpa only [annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_apply, one_apply] using hp.2.1
  have hmdiff : ∀ j : Fin N, ContMDiffOn (𝓡 2) (𝓡 n) 1 f
      {p | m64PolygonCut N j.castSucc ≤ p 0 ∧
        p 0 ≤ m64PolygonCut N j.succ ∧ 0 ≤ p 1 ∧ p 1 ≤ 1} := by
    intro j
    rw [hf, m64PolygonCut_cellSet]
    exact m64_polygon_cell_contMDiffOn polygon hH hgamma hpair j
  let hside : ∀ x : ℝ,
      M63MinimizingGeodesicSide g D 1 (gamma x)
        (polygon.map x) := fun x =>
    Classical.choose (m64_interpolator_side_of_short_pair g D
      (hshort x) (contMDiffOn_interpolator_slice hH (hpair_global x))
      (hprops (gamma x) (polygon.map x)))
  have hside_spec : ∀ x : ℝ, ∀ s : ℝ,
      (hside x).map s = H (s, gamma x, polygon.map x) := by
    intro x s
    dsimp [hside]
    exact Classical.choose_spec (m64_interpolator_side_of_short_pair g D
      (hshort x) (contMDiffOn_interpolator_slice hH (hpair_global x))
      (hprops (gamma x) (polygon.map x))) s
  have hmap : ∀ x s : ℝ, f (annulusPoint x s) = (hside x).map s := by
    intro x s
    rw [hf]
    simpa only [annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_apply, one_apply] using (hside_spec x s).symm
  have hcol0 := m64_horizontal_column_ae_of_metric_lipschitz g hL hLip
  exact m64AnnulusWitness_of_lipschitz_columns g D f hcontinuous hperiodic
    hlower hupper hL (by positivity) hLip hfinite hcol0 hcol1 hstrict
    hN (m64PolygonCut N) (m64PolygonCut_strictMono hN)
    m64PolygonCut_zero (m64PolygonCut_last hN) hmdiff hside hmap

end PoincareConjecture
