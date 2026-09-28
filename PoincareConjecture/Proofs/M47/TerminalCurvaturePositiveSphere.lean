import PoincareConjecture.Proofs.M47.TerminalCurvatureTransverse
import PoincareConjecture.Proofs.M47.TerminalCurvatureOpenSaturation
import PoincareConjecture.Proofs.M47.TerminalCurvatureSaturationBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47



theorem terminalCurvature_bounded_of_parallel_positive_sphere
    {M A : Type*} [TopologicalSpace M] [TopologicalSpace A]
    [T3Space M] [ConnectedSpace M] [CompactSpace A] [Nonempty A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) A]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 2) ∞ A]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hg : MetricComplete g)
    (hsec : D.NonnegativeSectionalCurvature)
    (V : (x : M) → TangentSpace (𝓡 3) x)
    (hV : ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V))
    (hunit : ∀ x, g.inner x (V x) (V x) = 1)
    (hparallel : ∀ x v, D.connection V x v = 0)
    (hnull : ∀ x, D.ricci x (V x) (V x) = 0)
    (F : A → M) (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ F)
    (hplane : ∀ z, ∃ a b : TangentSpace (𝓡 2) z,
      0 < D.curvatureTensor (F z)
        (mfderiv (𝓡 2) (𝓡 3) F z a) (mfderiv (𝓡 2) (𝓡 3) F z b)
        (mfderiv (𝓡 2) (𝓡 3) F z a) (mfderiv (𝓡 2) (𝓡 3) F z b)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  obtain ⟨Phi, hzero, hPhi, hcurve, hadd⟩ :=
    terminalCurvature_complete_unit_flow g hg V hV hunit
  have htransverse (z : A) :
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) F z) ∧
        V (F z) ∉ range (mfderiv (𝓡 2) (𝓡 3) F z) := by
    apply terminalCurvature_positive_plane_transverse D hD (F z) (hsec (F z))
      (mfderiv (𝓡 2) (𝓡 3) F z).toLinearMap (V (F z))
    · intro hz
      have hu := hunit (F z)
      simp [hz] at hu
    · exact hnull (F z)
    · exact hplane z
  exact terminalCurvature_bounded_of_parallel_saturation D hV hparallel hPhi hcurve
    hzero hadd (isCompact_range hF.continuous) (range_nonempty F)
    (terminalCurvature_sphere_saturation_open V Phi hzero hPhi hcurve hadd F hF htransverse)

end PoincareConjecture.M47
