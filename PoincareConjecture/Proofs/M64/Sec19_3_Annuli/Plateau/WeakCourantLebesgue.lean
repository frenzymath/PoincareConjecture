import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LogarithmicEnergyDrop
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusCircleTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeH1Radius












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)




theorem M64ObservedWeakAnnulus.exists_courant_lebesgue_circle
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (hei : IsClosedEmbedding e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {B : ℝ} (hb : ∀ q, ‖Q q‖ ≤ B) (hpos : ∀ q v, 0 ≤ Q q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : Metric.closedBall a rho ⊆ S)
    {N : ℕ} (hN : 0 < N) :
    ∃ (r : ℝ) (gamma : ℝ → M) (v : ℝ → E),
      r ∈ Icc (rho * Real.exp (-(N : ℝ))) rho ∧ 0 < r ∧
      Continuous gamma ∧ Function.Periodic gamma curvePeriod ∧
      gamma =ᵐ[circleMu] (fun x => A.map (a + r • angularPoint (x - Real.pi))) ∧
      MemLp v 2 circleMu ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod, e (gamma x) - e (gamma 0) = ∫ t in (0 : ℝ)..x, v t) ∧
      (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) ≤ 4 * C * A.energy Q / N ∧
      ∀ x ∈ Icc (0 : ℝ) curvePeriod, ∀ y ∈ Icc (0 : ℝ) curvePeriod,
        ‖e (gamma x) - e (gamma y)‖ ^ 2 ≤ 16 * curvePeriod * C * A.energy Q / N := by
  let R : ℕ → ℝ := fun j => rho * Real.exp (-(j : ℝ))
  let D : ℕ → ℝ := fun j => A.diskEnergy Q a (R j)
  obtain ⟨j, hj, hdrop⟩ := m64_exists_small_energy_drop D hN (A.diskEnergy_nonneg Q hpos a _)
  have hR (k : ℕ) : 0 < R k := mul_pos hrho (Real.exp_pos _)
  have hRle (k : ℕ) : R k ≤ rho :=
    mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hRsub (k : ℕ) : Metric.closedBall a (R k) ⊆ S :=
    (Metric.closedBall_subset_closedBall (hRle k)).trans hKS
  have hRsucc : R (j + 1) = R j * Real.exp (-1) := by
    simp only [R, Nat.cast_add, Nat.cast_one, neg_add_rev, Real.exp_add]
    ring
  have hD0 : D 0 = A.diskEnergy Q a rho := by simp [D, R]
  have hdrop' : A.diskEnergy Q a (R j) - A.diskEnergy Q a (R j * Real.exp (-1)) ≤
      A.energy Q / N := by
    have hbase := A.diskEnergy_le_energy Q hQ hei.isEmbedding hb hpos a rho
      (Metric.ball_subset_closedBall.trans hKS)
    have hh := hdrop.trans (div_le_div_of_nonneg_right (hD0 ▸ hbase) (by positivity : (0 : ℝ) ≤ N))
    simpa only [D, hRsucc] using hh
  obtain ⟨s, hs, htrace, hsE⟩ := m64UnitInterval_exists_le_integral_of_ae
    (A.angularEnergy a (R j)) (A.angularEnergy_integrable a (hR j) (hRsub j))
    (A.local_circle_traces hei a (hR j) (hRsub j))
  obtain ⟨gamma, w, hgamma, hperiod, hgammaAE, hv, hFTC, -, -, -, -, -⟩ := htrace
  let r := R j * Real.exp (-s)
  let v := fun x => m64MorreyPolarAngularColumn a (R j) (fun i p => A.column i p)
    (annulusPoint x s)
  have hr : 0 < r := mul_pos (hR j) (Real.exp_pos _)
  have hrexp : r = rho * Real.exp (-((j : ℝ) + s)) := by
    simp only [r, R, neg_add_rev, Real.exp_add]
    ring
  have hrlower : rho * Real.exp (-(N : ℝ)) ≤ r := by
    rw [hrexp]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hrho.le
    have hjr : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    linarith [hs.2]
  have hrupper : r ≤ rho := by
    rw [hrexp]
    exact mul_le_of_le_one_right hrho.le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (add_nonneg (Nat.cast_nonneg j) hs.1)))
  have hvE : (∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2) ≤ 4 * C * A.energy Q / N := by
    have hpolar := A.angularEnergy_integral_le_annular_energy Q hQ hei.isEmbedding hb hpos
      hC hcoercive a (hR j) (hRsub j)
    exact (hsE.trans hpolar).trans ((mul_le_mul_of_nonneg_left hdrop' (by positivity)).trans_eq
      (by ring))
  refine ⟨r, gamma, v, ⟨hrlower, hrupper⟩, hr, hgamma, hperiod, ?_, hv, hFTC, hvE, ?_⟩
  · simpa [m64MorreyPolarStrip, annulusPoint, r] using hgammaAE
  · intro x hx y hy
    have hosc := m64H1Trace_oscillation_sq_le (e ∘ gamma) v hv hFTC hx hy
    have hp : 0 ≤ 4 * curvePeriod := by unfold curvePeriod; positivity
    exact hosc.trans ((mul_le_mul_of_nonneg_left hvE hp).trans_eq (by ring))

end PoincareConjecture
