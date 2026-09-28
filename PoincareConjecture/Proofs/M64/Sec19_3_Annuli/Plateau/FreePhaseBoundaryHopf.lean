import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseBoundaryStressTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff ENNReal Manifold intervalIntegral

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem localized_boundary_hopf_endpoint
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) :
    (∫ y in (0 : ℝ)..1,
      m64HorizontalMoment (deriv eta)
        (fun p =>
          r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
            r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) y) = 0 := by
  let eta0 : ℝ → ℝ := fun x => eta x - eta 0
  have heta0 : ContDiff ℝ ∞ eta0 := heta.sub contDiff_const
  have hperiod0 : Function.Periodic eta0 curvePeriod := by
    intro x
    dsimp only [eta0]
    rw [hperiod x]
  have hzero0 : eta0 0 = 0 := by
    dsimp only [eta0]
    ring
  obtain ⟨_, _, hendpoint⟩ := localized_boundary_flux_primitive A hc0 hc1 hH0 hH1
    Q hQ hei hb r hmin heta0 hperiod0 hzero0
  have hderiv : ∀ x : ℝ, deriv eta0 x = deriv eta x := by
    intro x
    dsimp only [eta0]
    convert ((heta.differentiable (by simp) x).hasDerivAt.sub_const (eta 0)).deriv using 1
  simp only [m64HorizontalMoment] at hendpoint ⊢
  have hderiv' : deriv eta0 = deriv eta := funext hderiv
  rw [hderiv'] at hendpoint
  exact hendpoint

end PoincareConjecture.M64FreeWeakPhaseAnnulus
