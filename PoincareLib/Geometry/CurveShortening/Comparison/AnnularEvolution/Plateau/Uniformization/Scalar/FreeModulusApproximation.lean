import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.LipschitzAnnulusApproximation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.LocalFreeApproximation
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Actual free modulus approximation for every admissible annulus

Zero-area collars, physical polar descent, and relative area-controlled
mollification produce a C1 annulus with the original traces. The proved
annular uniformization of its positive smooth metric majorants then
constructs the modulus, positive degree-one boundary lifts, and genuine
admissible epsilon-energy competitor. No conformal supplier or fixed-trace
modulus reduction is assumed.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Every admissible annulus with C1 boundary curves produces an actual free-modulus
competitor with weighted energy below its area plus any positive error. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem exists_free_annulus_energy_lt_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
      StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
      (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
      ∃ B : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 n) 1 B.map Strip ∧
        IntegrableOn (fun p => (r * m60AreaGram g B.map p 0 0 +
          r⁻¹ * m60AreaGram g B.map p 1 1) / 2) m64AnnulusDomain ∧
        m64ClassicalWeightedGramEnergy g B r < A.area + eps := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : R1Space M := T2Space.r1Space
  let : RegularSpace M := RegularSpace.of_hasBasis
    isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
  let : T3Space M := ⟨⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨G, hG, hG0, hG1, -, hGA⟩ :=
    scalarAnnulus_exists_C1_physical_approximation A hc0 hc1 (half_pos heps)
  have hO : IsOpen {p : Plane | p ≠ 0} := isOpen_ne
  have hKO : scalarAnnulusDefining ⁻¹' Ici (0 : ℝ) ⊆ {p : Plane | p ≠ 0} := by
    intro p hp
    have hnorm := ((scalarAnnulusDefining_nonneg p).mp hp).1
    exact norm_pos_iff.mp (zero_lt_one.trans_le hnorm)
  have hzero : (fun x => G (scalarCoverMap (1, x / curvePeriod))) = c0 := funext hG0
  have hone : (fun x => G (scalarCoverMap (2, x / curvePeriod))) = c1 := funext hG1
  have hcandidate := exists_localC1_free_annulus_energy_lt_area_fullStrip
    g G hO hKO hG (eps / 2) (half_pos heps)
  rw [hzero, hone] at hcandidate
  obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, hBE⟩ := hcandidate
  exact ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, by linarith⟩

/-- The constructed arbitrary-annulus competitors establish the original free
conformal-modulus approximation predicate for C1 boundary curves. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem m64FreeConformalModulusApproximation_of_C1
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A eps heps
  obtain ⟨r, hr, sigma0, sigma1, -, -, -, -, -, -, B, -, hBI, hBE⟩ :=
    exists_free_annulus_energy_lt_area A hc0 hc1 heps
  exact ⟨r, hr, sigma0, sigma1, B, hBI, hBE.le⟩

end PoincareMT.M64Uniformization
