import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import PoincareConjecture.Definitions.Ch19.RampEstimates










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



noncomputable def constantLoopFamily {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] (x : M) :
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
  ⟨fun _ => constantC1Loop x, continuous_const⟩








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

end PoincareConjecture
