import PoincareLib.Geometry.Riemannian.LoopSpace.Width
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Basic

/-!
# Short-loop triviality and small-area disk statements

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

/-!
The three conclusions used from Lemma 18.27 and Corollary 18.28. The first
returns the identity in the actual based pi2 of the project C1 free-loop
space, so it does not assume the later pi2(loop-space)-pi3 identification.
The raw-family conclusion retains the connectedness hypothesis. The last
supplies a concrete Lipschitz filling with the original allowed circle
reparameterization.
-/
structure RepairedShortLoopTrivialityData where
  short_loop_family_trivial : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M))
      (basepoint : M)
      (pi_two_trivial : Subsingleton
        (HomotopyGroup.Pi 2 M basepoint)),
      letI := pi_two_trivial
      ∃ ζ : ℝ, 0 < ζ ∧
        ∀ source : FreeTwoSphereFamily (M := M),
          source.basepoint = basepoint →
          (∀ c : LoopTwoSphere,
            freeLoopLength g (source.family c) < ζ) →
              source.homotopy_class = 1
  /-- Raw-family version used by M65's un-decorated output.  This is an
  explicit reformulation of the all-short argument, rather than an assumed
  arbitrary class predicate. -/
  raw_short_loop_family_trivial : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M))
      (_connected : IsConnected (Set.univ : Set M))
      (basepoint : M)
      (pi_two_trivial : Subsingleton
        (HomotopyGroup.Pi 2 M basepoint)),
      letI := pi_two_trivial
      ∃ ζ : ℝ, 0 < ζ ∧
        ∀ source : ContinuousMap LoopTwoSphere
            (C1FreeLoopSpace (M := M)),
          (∀ c, IsNullHomotopicLoop (source c)) →
          (∀ c, freeLoopLength g (source c) < ζ) →
            source.Homotopic (constantLoopFamily basepoint)
  small_loop_filling : ∀ {M : Type u} [TopologicalSpace M]
      [T2Space M] [SecondCountableTopology M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M)
      (_compact : IsCompact (Set.univ : Set M)),
      ∀ η : ℝ, 0 < η →
        ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
          ∀ γ : C1FreeLoopSpace (M := M),
            freeLoopLength g γ < ζ →
              ∃ D : LipschitzSpanningDisk g γ, D.area < η

end PoincareMT
