import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedLowerReflection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LowerReflectionEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyLocalRescaling










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain




theorem lower_reflected_column_closed_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x0 rho K beta : ℝ}
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ O)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta) :
    ∀ i : Fin 2, ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r, ‖A.lowerReflectedColumn i p‖ ^ 2) ≤
        (2 * K) * r ^ beta := by
  have hi (i : Fin 2) : IntegrableOn (fun p => ‖A.column i p‖ ^ 2) S :=
    (Lp.memLp (A.column i)).norm.integrable_sq
  have hsum : IntegrableOn (fun p => ∑ i : Fin 2, ‖A.column i p‖ ^ 2) S :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hone (i : Fin 2) (b : LoopPlane) (hb : b ∈ closedBall (annulusPoint x0 0) rho)
      (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) rho) :
      (∫ p in closedBall b r ∩ S, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta := by
    apply le_trans (integral_mono_ae ((hi i).mono_set inter_subset_right)
      (hsum.mono_set inter_subset_right) ?_) (henergy b hb r hr)
    exact Eventually.of_forall fun p => Finset.single_le_sum
      (fun j _ => sq_nonneg ‖A.column j p‖) (Finset.mem_univ i)
  have haxis : m60PlaneReflection (annulusPoint x0 0) = annulusPoint x0 0 := by
    ext i
    fin_cases i <;> simp [m60PlaneReflection_apply, annulusPoint]
  intro i b hb r hr
  have hball : closedBall b r ⊆ O := (closedBall_subset_closedBall'
    (show r + dist b (annulusPoint x0 0) ≤ 2 * rho from by
      linarith [mem_closedBall.mp hb, hr.2])).trans hsub
  have hRb : m60PlaneReflection b ∈ closedBall (annulusPoint x0 0) rho := by
    rw [mem_closedBall, ← haxis, LinearIsometryEquiv.dist_map]
    exact hb
  have he : ‖if i = 0 then (1 : ℝ) else -1‖ = 1 := by
    split_ifs <;> norm_num
  calc
    _ = (∫ p in closedBall b r ∩ S, ‖A.column i p‖ ^ 2) +
        ∫ p in closedBall (m60PlaneReflection b) r ∩ S, ‖A.column i p‖ ^ 2 :=
      m64LowerReflection_integral_norm_sq (Lp.memLp (A.column i)) he hball
    _ ≤ K * r ^ beta + K * r ^ beta := add_le_add (hone i b hb r hr)
      (hone i _ hRb r hr)
    _ = _ := by ring



theorem lower_reflected_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x0 rho K beta : ℝ}
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ O)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta) :
    ∀ i : Fin 2, ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in ball b r, ‖A.lowerReflectedColumn i p‖ ^ 2) ≤ (2 * K) * r ^ beta := by
  intro i b hb r hr
  have hball : closedBall b r ⊆ O := (closedBall_subset_closedBall'
    (show r + dist b (annulusPoint x0 0) ≤ 2 * rho from by
      linarith [mem_closedBall.mp hb, hr.2])).trans hsub
  have hi : IntegrableOn (fun p => ‖A.lowerReflectedColumn i p‖ ^ 2) (closedBall b r) :=
    IntegrableOn.mono_set (A.lower_reflected_memLp.2 i).norm.integrable_sq hball
  exact (setIntegral_mono_set hi (Eventually.of_forall fun p => sq_nonneg _)
    (Eventually.of_forall fun p hp => ball_subset_closedBall hp)).trans
    (A.lower_reflected_column_closed_growth hsub henergy i b hb r hr)



theorem lower_reflected_energy_closed_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x0 rho K beta : ℝ}
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ O)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta) :
    ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r, ∑ i : Fin 2, ‖A.lowerReflectedColumn i p‖ ^ 2) ≤
        (4 * K) * r ^ beta := by
  intro b hb r hr
  have hball : closedBall b r ⊆ O := (closedBall_subset_closedBall'
    (show r + dist b (annulusPoint x0 0) ≤ 2 * rho from by
      linarith [mem_closedBall.mp hb, hr.2])).trans hsub
  have hi (i : Fin 2) : IntegrableOn
      (fun p => ‖A.lowerReflectedColumn i p‖ ^ 2) (closedBall b r) :=
    IntegrableOn.mono_set (A.lower_reflected_memLp.2 i).norm.integrable_sq hball
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ ≤ ∑ _i : Fin 2, (2 * K) * r ^ beta :=
      Finset.sum_le_sum fun i _ => A.lower_reflected_column_closed_growth hsub henergy i b hb r hr
    _ = _ := by simp; ring




theorem lower_holder_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {x0 rho K beta : ℝ} (hrho : 0 < rho)
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ O)
    (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.column i p‖ ^ 2) ≤ K * r ^ beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U : LoopPlane → E,
      ContinuousOn U (closedBall (annulusPoint x0 0) (rho / 2)) ∧
      U =ᵐ[volume.restrict (ball (annulusPoint x0 0) (rho / 2))] A.lowerReflectedValue ∧
      ∀ x ∈ closedBall (annulusPoint x0 0) (rho / 2),
        ∀ y ∈ closedBall (annulusPoint x0 0) (rho / 2),
        dist (U x) (U y) ≤ C * (dist x y) ^ (beta / 2) := by
  have hball : ball (annulusPoint x0 0) (rho * 2) ⊆ O := by
    rw [mul_comm rho 2]
    exact ball_subset_closedBall.trans hsub
  exact m64Morrey_local_disk_holder_representative hrho
    (A.lower_reflected_memLp.1.mono_measure (Measure.restrict_mono hball le_rfl))
    (fun i => (A.lower_reflected_memLp.2 i).mono_measure (Measure.restrict_mono hball le_rfl))
    (fun i b => (A.lower_reflected_weak i b).restrict isOpen_ball hball)
    (by positivity : 0 ≤ 2 * K) hbeta (A.lower_reflected_column_power_growth hsub henergy)

end PoincareConjecture.M64ObservedWeakAnnulus
