import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamLocalEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarColumnEstimate
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarAEPullback
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "mu" => volume.restrict S



theorem seam_polar_angular_memLp
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    MemLp (m64MorreyPolarAngularColumn a rho
      (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E))) 2 mu :=
  (m64WeakMap_polar_strong_approximation m64AnnulusSeamDomain_isOpen a hrho hKO
    (e ∘ m64AnnulusSeamExtend A.map)
    (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E))
    A.seam_extension_memLp.1 A.seam_extension_memLp.2 A.seam_extension_weak_partial).2.1



theorem seamAngularEnergy_integrable
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    IntegrableOn (A.seamAngularEnergy a rho) (Icc (0 : ℝ) 1) volume := by
  have hz := A.seam_polar_angular_memLp a hrho hKO
  have hi := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  exact (m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hi).integral_prod_right



theorem seamAngularEnergy_integral_le_annular_energy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q w, 0 ≤ Q q w w)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (w : E), w ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖w‖ ^ 2 ≤ C * Q q w w)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKO : Metric.closedBall a rho ⊆ O) :
    (∫ s in Icc (0 : ℝ) 1, A.seamAngularEnergy a rho s) ≤
      4 * C * (A.seamDiskEnergy Q a rho - A.seamDiskEnergy Q a (rho * Real.exp (-1))) := by
  let F := A.seamEnergyDensity Q
  let U := m64AnnulusSeamExtend A.map
  let V := fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)
  let P := m64MorreyPolarStrip a rho
  let J := fun p : LoopPlane => (rho * Real.exp (-p 1)) ^ 2
  let Z := m64MorreyPolarAngularColumn a rho V
  have hF : IntegrableOn F (Metric.closedBall a rho) volume :=
    (A.seamEnergyDensity_integrable Q hQ hei hb).mono_set hKO
  have hFpos : ∀ p, 0 ≤ F p := A.seamEnergyDensity_nonneg Q hpos
  have hz := A.seam_polar_angular_memLp a hrho hKO
  have hzi : IntegrableOn (fun p => ‖Z p‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  have hwi : IntegrableOn (fun p => J p * F (P p)) S volume :=
    m64MorreyPolarStrip_weighted_integrable a hrho hF
  have ht (i : Fin 2) := m64MorreyPolarStrip_ae a hrho
    (ae_restrict_of_ae_restrict_of_subset hKO (A.seam_extension_tangent i))
  have hpoint : ∀ᵐ p ∂mu, ‖Z p‖ ^ 2 ≤ 4 * C * (J p * F (P p)) := by
    filter_upwards [ht 0, ht 1] with p h0 h1
    have hsum := add_le_add
      (hcoercive (U (P p)) (V 0 (P p)) h0)
      (hcoercive (U (P p)) (V 1 (P p)) h1)
    calc
      _ ≤ 2 * J p * (‖V 0 (P p)‖ ^ 2 + ‖V 1 (P p)‖ ^ 2) :=
        m64MorreyPolarAngularColumn_norm_sq_le a rho V p
      _ ≤ 2 * J p * (C * Q (U (P p)) (V 0 (P p)) (V 0 (P p)) +
          C * Q (U (P p)) (V 1 (P p)) (V 1 (P p))) :=
        mul_le_mul_of_nonneg_left hsum (by dsimp [J]; positivity)
      _ = _ := by dsimp only [F, U, V, seamEnergyDensity]; ring
  have hclosed : (∫ p in Metric.closedBall a rho, F p) -
      (∫ p in Metric.closedBall a (rho * Real.exp (-1)), F p) =
      A.seamDiskEnergy Q a rho - A.seamDiskEnergy Q a (rho * Real.exp (-1)) := by
    unfold seamDiskEnergy
    rw [setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume a rho),
      setIntegral_congr_set (M60.haar_ball_ae_eq_closedBall volume a (rho * Real.exp (-1)))]
  calc
    _ = ∫ p in S, ‖Z p‖ ^ 2 :=
      (m64AnnulusInteriorIntegral_eq_iterated_swap_integrable (fun p => ‖Z p‖ ^ 2) hzi).symm
    _ ≤ ∫ p in S, 4 * C * (J p * F (P p)) := integral_mono_ae hzi (hwi.const_mul _) hpoint
    _ = 4 * C * ∫ p in S, J p * F (P p) := integral_const_mul _ _
    _ ≤ 4 * C * ((∫ p in Metric.closedBall a rho, F p) -
        ∫ p in Metric.closedBall a (rho * Real.exp (-1)), F p) :=
      mul_le_mul_of_nonneg_left
        (m64MorreyPolarStrip_weighted_integral_le_annulus a hrho hF hFpos) (by positivity)
    _ = _ := by rw [hclosed]

end PoincareConjecture.M64ObservedWeakAnnulus
