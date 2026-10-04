import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.MinimizerContinuity
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.WeakMinimizer

/-!
# A continuous interior energy minimizer from an admissible annulus

The seed supplies the weak boundary class. The direct method and the
proved local energy growth construct an interior-continuous minimizer.
The modulus and boundary parametrizations are still fixed at this stage.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

/-- Construct an actual interior-continuous weak energy minimum from an admissible annulus.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Annulus_exists_interior_continuous_weak_energy_minimizer
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A0 : M64Annulus g c0 c1) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ Continuous B ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : M) (v : TangentSpace (𝓡 n) q),
        B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) ∧
      ContinuousOn L.map (interior m64AnnulusDomain) ∧
      (∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, L.energy B ≤ W.energy B) ∧
      ∀ A : M64Annulus g c0 c1,
        L.energy B ≤ ∫ p in interior m64AnnulusDomain, m60EnergyDensity g A.map p := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨W0, -, -⟩ := m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨B, W, hB, hpos, hsymm, hgram, hW⟩ :=
    m64ObservedWeakAnnulus_exists_minimizer g e he1 hei hread W0
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he1 B hgram
  obtain ⟨L, hLcont, -, -, -, hL⟩ :=
    W.continuous_representative g he1 hei hread B hB hpos hC hcoercive hW
  have hdiag := m64ObservedMetric_tangent_diagonal g e he1 B hgram
  refine ⟨m, e, B, L, he, hei, hread, hB, hpos, hsymm, hdiag, hLcont, hL, ?_⟩
  intro A
  obtain ⟨V, -, henergy⟩ := m64ObservedWeakAnnulus_exists_seed_with_energy A e he1 B hdiag
  exact (hL V).trans_eq henergy

end PoincareMT
