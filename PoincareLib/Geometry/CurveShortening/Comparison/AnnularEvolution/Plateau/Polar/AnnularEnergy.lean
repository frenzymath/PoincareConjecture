import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.LocalEnergy
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.ColumnEstimate
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.AEPullback
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Homotopy.Null.Sphere

/-!
# Angular energy is controlled by the actual logarithmic annulus

The polar Jacobian cancels the squared radius in the angular column.
The image avoids the inner disk, so the bound is the difference of the
two disk energies, not the energy of the entire outer disk.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

namespace PoincareMT

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

namespace M64ObservedWeakAnnulus

/-- The actual polar angular weak column belongs to L2 on the strip. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem polar_angular_memLp
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : Metric.closedBall a rho ⊆ S) :
    MemLp (m64MorreyPolarAngularColumn a rho (fun i p => A.column i p)) 2 mu :=
  (m64WeakMap_polar_strong_approximation isOpen_interior a hrho hKS
    (e ∘ A.map) (fun i p => A.column i p) A.observed_memLp
    (fun i => Lp.memLp (A.column i)) A.weak_partial).2.1

/-- The actual circle angular energy is integrable in logarithmic radius. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem angularEnergy_integrable
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : Metric.closedBall a rho ⊆ S) :
    IntegrableOn (A.angularEnergy a rho) (Icc (0 : ℝ) 1) volume := by
  have hz := A.polar_angular_memLp a hrho hKS
  have hi := (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  exact (m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hi).integral_prod_right

/-- Actual angular energy is bounded by the intrinsic shell energy with the explicit
coercivity factor. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem angularEnergy_integral_le_annular_energy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : Metric.closedBall a rho ⊆ S) :
    (∫ s in Icc (0 : ℝ) 1, A.angularEnergy a rho s) ≤
      4 * C * (A.diskEnergy Q a rho - A.diskEnergy Q a (rho * Real.exp (-1))) := by
  let F := fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let P := m64MorreyPolarStrip a rho
  let J := fun p : LoopPlane => (rho * Real.exp (-p 1)) ^ 2
  let Z := m64MorreyPolarAngularColumn a rho (fun i p => A.column i p)
  have hF : IntegrableOn F (Metric.closedBall a rho) volume :=
    (A.energy_integrable Q hQ hei hb).mono_set hKS
  have hFpos (p : LoopPlane) : 0 ≤ F p :=
    div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)
  have hz := A.polar_angular_memLp a hrho hKS
  have hzi : IntegrableOn (fun p => ‖Z p‖ ^ 2) S volume :=
    (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).mp hz
  have hwi : IntegrableOn (fun p => J p * F (P p)) S volume :=
    m64MorreyPolarStrip_weighted_integrable a hrho hF
  have ht (i : Fin 2) := m64MorreyPolarStrip_ae a hrho
    (ae_restrict_of_ae_restrict_of_subset hKS (A.tangent i))
  have hpoint : ∀ᵐ p ∂mu, ‖Z p‖ ^ 2 ≤ 4 * C * (J p * F (P p)) := by
    filter_upwards [ht 0, ht 1] with p h0 h1
    have hsum := add_le_add
      (hcoercive (A.map (P p)) (A.column 0 (P p)) h0)
      (hcoercive (A.map (P p)) (A.column 1 (P p)) h1)
    calc
      _ ≤ 2 * J p * (‖A.column 0 (P p)‖ ^ 2 + ‖A.column 1 (P p)‖ ^ 2) :=
        m64MorreyPolarAngularColumn_norm_sq_le a rho (fun i p => A.column i p) p
      _ ≤ 2 * J p * (C * Q (A.map (P p)) (A.column 0 (P p)) (A.column 0 (P p)) +
          C * Q (A.map (P p)) (A.column 1 (P p)) (A.column 1 (P p))) :=
        mul_le_mul_of_nonneg_left hsum (by dsimp [J]; positivity)
      _ = _ := by dsimp only [F]; ring
  have hclosed : (∫ p in Metric.closedBall a rho, F p) -
      (∫ p in Metric.closedBall a (rho * Real.exp (-1)), F p) =
      A.diskEnergy Q a rho - A.diskEnergy Q a (rho * Real.exp (-1)) := by
    unfold diskEnergy
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

end M64ObservedWeakAnnulus

end PoincareMT
