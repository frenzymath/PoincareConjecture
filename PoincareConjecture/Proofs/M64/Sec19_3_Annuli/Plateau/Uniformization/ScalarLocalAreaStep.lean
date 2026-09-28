import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarChartLocalLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem scalar_exists_local_area_step
    (g : RiemannianMetric n M) (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (f : Plane → M) {O K : Set Plane} (hO : IsOpen O)
    (hf : ContinuousOn f O) (hlocal : ScalarLocallyChartLipschitz (n := n) f O)
    {rho : Plane → ℝ} (hrho : ContDiff ℝ ∞ rho)
    (hcompact : HasCompactSupport rho) (hrange : ∀ x, rho x ∈ Icc 0 1)
    (hsupp : tsupport rho ⊆ O) (hchart : MapsTo f (tsupport rho) e.source)
    (hK : MeasurableSet K) (hCK : tsupport rho ⊆ K)
    (harea : IntegrableOn (m60AreaDensity g f) K) {eps : ℝ} (heps : 0 < eps) :
    ∃ F : Plane → M,
      ContinuousOn F O ∧ ScalarLocallyChartLipschitz (n := n) F O ∧
      (∀ x, x ∉ tsupport rho → F =ᶠ[𝓝 x] f) ∧
      (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) 1 f x → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x, rho =ᶠ[𝓝 x] 1 → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x, dist (F x) (f x) < eps) ∧
      IntegrableOn (m60AreaDensity g F) K ∧
      (∫ x in K, m60AreaDensity g F x) < (∫ x in K, m60AreaDensity g f x) + eps := by
  obtain ⟨L, V, hV, hCV, -, hfV, hcoord⟩ :=
    hlocal.compact_patch hf hO hcompact hsupp e he hchart
  obtain ⟨F, B, hFc, hFL, hFm, hFa, hFp, hFs, hFclose, hFI, hFA⟩ :=
    scalar_exists_chart_area_step g e he hei f hO hV hf hfV hcoord
      hrho hcompact hrange hCV hK hCK harea heps
  exact ⟨F, hFc, hlocal.of_chart_replacement hV hCV e hei hFm hFL hFa,
    hFa, hFp, hFs, hFclose, hFI, hFA⟩

end PoincareConjecture.M64Uniformization
