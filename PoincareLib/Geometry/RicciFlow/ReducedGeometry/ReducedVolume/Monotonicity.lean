import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.WeakInequality.WeakInequalities
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Minimum.MinimumBound
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.VolumeComparison
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.VolumePositive
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.RestrictedVolume
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Rigidity.EuclideanRigidity

/-!
# Reduced-volume proof assembly

The owned analytic, measure, monotonicity and rigidity producers assemble the
complete unchanged contract relative to the supplied L-geometry theories.
Both predecessor interfaces remain explicit theorem inputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- M10: for a connected ordinary Ricci flow complete with one full-curvature
bound on [T-taumax,T], M08 and M09 give continuity, local Lipschitz regularity,
one open regular spacetime locus with null complement on every interior slice,
and locally bounded derivatives. Both complete weak reduced-length integrands
are integrable and satisfy their stated inequalities. The spatial minimum is
attained and at most n/2. The calibrated reduced-volume density is integrable;
its total integral is positive, at most (4*pi)^(n/2), nonincreasing for
0 < tau < taumax, and tends to that value at zero. The stated open regular
backward L-star-shaped domains also have nonincreasing reduced volume.
Equality at one interior time gives one static Euclidean identification
over the whole closed interval [T-tau,T].

Sources: Morgan-Tian Corollary 6.67 and Claims 6.68-6.69, pp. 139-140;
Definition 6.70, p. 140, and Lemma 6.71, p. 141; Proposition 6.78 and
Corollary 6.79, pp. 143-145; Theorem 6.80 and Proposition 6.81, pp. 145-146;
Proposition 7.5 and Corollary 7.6, pp. 151-152; Theorem 7.10 and Claim 7.11,
pp. 154-156; Theorem 7.13 and its proof, pp. 156-164, including Lemma 7.15
through Corollary 7.24; Theorem 7.26 and Proposition 7.27, pp. 165-167.
Use the corrections in `reviews/errata/2026-09-13-reduced-length-source.md`
and M08's pullback connection transport. The density follows the book's
unnormalized convention. `reviews/contracts/M10-round1.md` gives the complete
source derivation and the boundaries of its ordinary-flow applications. -/
theorem reducedVolumeMonotonicity
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax) :
    Nonempty (ReducedVolumeTheory F T τmax) := by
  let G (p : M) := Classical.choice (hDifferential.exponential_geometry p)
  exact ⟨{
    measure_regularity := ReducedVolume.reducedLength_measure_regularity hL hDifferential hwindow
    weak_inequalities := ReducedVolume.reducedLength_weak_inequalities hL hDifferential hwindow
    minimum_bound := fun p _ hτ hmax ↦
      ReducedVolume.reducedLength_minimum_bound hL hDifferential hT hwindow hcurvature p hτ hmax
    density_integrable := fun p _ hτ hmax ↦
      ReducedVolume.reducedVolumeDensity_integrable hL hDifferential (G p) hτmax hT hwindow
        hcurvature hτ hmax
    volume_bounds := fun p _ hτ hmax ↦
      ⟨ReducedVolume.reducedVolume_pos hL hDifferential (G p) hτmax hT hwindow hcurvature hτ hmax,
        ReducedVolume.reducedVolume_le_euclidean hL hDifferential (G p) hτmax hT hwindow
          hcurvature hτ hmax⟩
    monotone := fun p ↦
      ReducedVolume.reducedVolume_antitoneOn hL hDifferential (G p) hτmax hT hwindow hcurvature
    zero_time_limit := fun p ↦
      ReducedVolume.reducedVolume_tendsto_zero hL hDifferential (G p) hτmax hT hwindow hcurvature
    open_domain_monotone := fun p _ hA ↦
      ReducedVolume.reducedVolumeOn_antitoneOn hL hDifferential (G p) hτmax hT hwindow hcurvature hA
    euclidean_rigidity := fun p _ hτ hmax heq ↦
      ReducedVolume.staticEuclideanFlowOn_of_reducedVolume_eq hL hDifferential (G p) hτmax hT
        hwindow hcurvature hτ hmax heq }⟩

end PoincareMT
