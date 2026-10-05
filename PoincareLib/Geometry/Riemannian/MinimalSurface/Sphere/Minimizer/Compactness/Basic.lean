import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Compactness.Bounded
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.BubbleLimit.StrongEquation
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Sequence

/-! The actual maximum-gradient limit of perturbed non-null minima. -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareMT

open M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

/-- Actual normalized C1 compactness, the literal weak limit equation,
and puncture removal produce the maximum-gradient sphere used in the
least-area argument. The sole remaining shared service is planar
alpha-one smoothness; the strong equation is derived from the same weak
record here. Source: SU Theorems 4.4-4.7 and corrected MT Lemma 18.10. -/
theorem m60PerturbedMinimizers_maxGradientLimit (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g) : SUMaxGradientCompactnessProducer g := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  intro alpha f ha har hf hn hmin heq
  have htotal := (m60PerturbedMinimizers_area_energy_tendsto g alpha f ha
    (fun j => (har j).1) hf hn hmin).2.1
  have ha2 (j : ℕ) : 1 ≤ alpha j ∧ alpha j ≤ 2 := ⟨(har j).1, by linarith [(har j).2]⟩
  have equation := fun (p : M) (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)) (center : LoopPlane) (radius : ℝ)
    (S : SUWeakAlphaCoordinate g p 1 u V center radius) (hs : ContDiffAt ℝ ∞ u center) =>
      suWeakAlphaCoordinate_harmonic_of_smooth S hs
  by_cases hbounded : ∃ B : ℝ, ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B
  · obtain ⟨B, hB⟩ := hbounded
    exact suBoundedGradient_sphereLimit g regular equation alpha f hf hn ha ha2 heq htotal hB
  · exact suUnboundedGradient_sphereLimit g regular equation alpha f hf ha ha2 heq htotal hbounded

end PoincareMT
