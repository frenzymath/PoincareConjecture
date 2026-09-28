import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarCircleColumn

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

namespace M64ObservedWeakAnnulus

def diskEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (a : LoopPlane) (r : ℝ) : ℝ :=
  ∫ p in Metric.ball a r, (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2

def angularEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) curvePeriod,
    ‖m64MorreyPolarAngularColumn a rho (fun i p => A.column i p) (annulusPoint x s)‖ ^ 2

theorem diskEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) : 0 ≤ A.diskEnergy Q a r :=
  integral_nonneg fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)

theorem angularEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : 0 ≤ A.angularEnergy a rho s :=
  integral_nonneg fun _ => sq_nonneg _

theorem diskEnergy_le_energy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) (hball : Metric.ball a r ⊆ S) :
    A.diskEnergy Q a r ≤ A.energy Q :=
  setIntegral_mono_set (A.energy_integrable Q hQ hei hb)
    (Eventually.of_forall fun p =>
      div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))
    (Eventually.of_forall hball)

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

end PoincareConjecture
