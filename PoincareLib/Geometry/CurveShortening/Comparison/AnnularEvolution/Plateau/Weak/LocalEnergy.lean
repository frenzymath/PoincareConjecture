import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementEnergy
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Polar.CircleColumn

/-! The actual disk and angular energies used in the local growth estimate.
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

namespace M64ObservedWeakAnnulus

/-- The local intrinsic disk energy is the integral of the actual weak annular energy
density. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def diskEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (a : LoopPlane) (r : ℝ) : ℝ :=
  ∫ p in Metric.ball a r, (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2

/-- The angular circle energy uses the actual observed polar column and target metric. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def angularEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) curvePeriod,
    ‖m64MorreyPolarAngularColumn a rho (fun i p => A.column i p) (annulusPoint x s)‖ ^ 2

/-- Semipositivity of the observed metric makes every local disk energy nonnegative. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem diskEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) : 0 ≤ A.diskEnergy Q a r :=
  integral_nonneg fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)

/-- Semipositivity of the observed metric makes every angular circle energy nonnegative.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem angularEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : 0 ≤ A.angularEnergy a rho s :=
  integral_nonneg fun _ => sq_nonneg _

/-- A disk inside the original rectangle has energy no larger than the full weak annulus.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem diskEnergy_le_energy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) (hball : Metric.ball a r ⊆ S) :
    A.diskEnergy Q a r ≤ A.energy Q :=
  setIntegral_mono_set (A.energy_integrable Q hQ hei hb)
    (Eventually.of_forall fun p =>
      div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))
    (Eventually.of_forall hball)

/-- Actual local disk energy is monotone for nested disks inside the original rectangle.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem diskEnergy_mono (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) {r R : ℝ} (hrR : r ≤ R) (hball : Metric.ball a R ⊆ S) :
    A.diskEnergy Q a r ≤ A.diskEnergy Q a R :=
  setIntegral_mono_set ((A.energy_integrable Q hQ hei hb).mono_set hball)
    (Eventually.of_forall fun p =>
      div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))
    (Eventually.of_forall (Metric.ball_subset_ball hrR))

end M64ObservedWeakAnnulus

end PoincareMT
