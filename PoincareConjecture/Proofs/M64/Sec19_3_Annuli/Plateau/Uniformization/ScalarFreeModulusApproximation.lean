import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLipschitzAnnulusApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalFreeApproximation
import Mathlib.Topology.Metrizable.Uniformity















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





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





theorem m64FreeConformalModulusApproximation_of_C1
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A eps heps
  obtain ⟨r, hr, sigma0, sigma1, -, -, -, -, -, -, B, -, hBI, hBE⟩ :=
    exists_free_annulus_energy_lt_area A hc0 hc1 heps
  exact ⟨r, hr, sigma0, sigma1, B, hBI, hBE.le⟩

end PoincareConjecture.M64Uniformization
