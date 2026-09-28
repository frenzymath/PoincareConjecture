import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityLocalConclusion
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityGlobal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalNormalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.Attainment










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture




theorem m65PlateauBoundaryRegularityInput_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (gamma : C1FreeLoopSpace (M := M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) t ≠ 0)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    M65PlateauBoundaryRegularityInput g connection e gamma a b c := by
  intro F hmin hconf f hf
  apply M65Boundary.exists_global_boundary_extension connection F f hf
  intro p hp
  obtain ⟨r, q, hr, hq, heq, htrace⟩ :=
    M65Boundary.weakDisk_boundary_local_contMDiff g connection he hinj hemb compact
      gamma.continuous hsmooth hregular F
      (F.normalized_minimum_is_minimum g he.continuous gamma.continuous hab hac hbc hmin)
      hconf hf hp
  exact ⟨r, hr, q, hq, heq, htrace⟩

end PoincareConjecture
