import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryLocalEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

open M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem boundaryAngularEnergy_shell_bound
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hr : rho < 1) :
    IntegrableOn (fun s => A.boundaryAngularEnergy x (rho * Real.exp (-s))) (Icc (0 : ℝ) 1) ∧
      (∫ s in Icc (0 : ℝ) 1, A.boundaryAngularEnergy x (rho * Real.exp (-s))) ≤
        4 * C * (A.boundaryDiskEnergy B x rho -
          A.boundaryDiskEnergy B x (rho * Real.exp (-1))) := by
  let F := fun p => (B (A.map p) (A.column 0 p) (A.column 0 p) +
    B (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let P := boundaryPolarStrip x rho
  let J := fun p : LoopPlane => (rho * Real.exp (-p 1)) ^ 2 / 2
  let Z := boundaryPolarColumn x rho (fun i p => A.column i p)
  have hsub := upperBoundaryShell_subset_interior hx hP hr
  have hF := (A.energy_integrable B hB hei hb).mono_set hsub
  have hFpos (p : LoopPlane) : 0 ≤ F p :=
    div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)
  obtain ⟨hweighted, hshell⟩ := boundaryPolarStrip_weighted_integral x hrho hF hFpos
  have hZ := boundaryPolarColumn_memLp x hrho (fun i p => A.column i p)
    (fun i => (Lp.memLp (A.column i)).mono_measure (Measure.restrict_mono hsub le_rfl))
  have hZi : IntegrableOn (fun p => ‖Z p‖ ^ 2) S := hZ.norm.integrable_sq
  have htan (i : Fin 2) := boundaryPolarStrip_ae x hrho
    (ae_restrict_of_ae_restrict_of_subset hsub (A.tangent i))
  have hpoint : ∀ᵐ p ∂volume.restrict S, ‖Z p‖ ^ 2 ≤ 8 * C * (J p * F (P p)) := by
    filter_upwards [htan 0, htan 1] with p h0 h1
    have hsum := add_le_add
      (hcoercive (A.map (P p)) (A.column 0 (P p)) h0)
      (hcoercive (A.map (P p)) (A.column 1 (P p)) h1)
    calc
      _ ≤ 2 * (rho * Real.exp (-p 1)) ^ 2 *
          (‖A.column 0 (P p)‖ ^ 2 + ‖A.column 1 (P p)‖ ^ 2) :=
        boundaryPolarColumn_norm_sq_le x rho (fun i p => A.column i p) p
      _ ≤ 2 * (rho * Real.exp (-p 1)) ^ 2 *
          (C * B (A.map (P p)) (A.column 0 (P p)) (A.column 0 (P p)) +
            C * B (A.map (P p)) (A.column 1 (P p)) (A.column 1 (P p))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp only [F, J]; ring
  have henergy : (∫ p in S, ‖Z p‖ ^ 2) ≤
      8 * C * ∫ p in upperBoundaryShell x rho, F p := by
    calc
      _ ≤ ∫ p in S, 8 * C * (J p * F (P p)) :=
        integral_mono_ae hZi (hweighted.const_mul _) hpoint
      _ = 8 * C * ∫ p in S, J p * F (P p) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hshell (by positivity)
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hZi
  have hangular (s : ℝ) : (∫ t in Icc (0 : ℝ) curvePeriod, ‖Z (annulusPoint t s)‖ ^ 2) =
      2 * A.boundaryAngularEnergy x (rho * Real.exp (-s)) :=
    boundaryPolarColumn_integral x rho s (fun i p => A.column i p)
  have hi : IntegrableOn (fun s => A.boundaryAngularEnergy x (rho * Real.exp (-s)))
      (Icc (0 : ℝ) 1) := by
    apply (hprod.integral_prod_right.const_mul (1 / 2 : ℝ)).congr
    filter_upwards with s
    change (1 / 2 : ℝ) * (∫ t in Icc (0 : ℝ) curvePeriod, ‖Z (annulusPoint t s)‖ ^ 2) = _
    rw [hangular]
    ring
  have hid : (∫ p in S, ‖Z p‖ ^ 2) =
      2 * ∫ s in Icc (0 : ℝ) 1, A.boundaryAngularEnergy x (rho * Real.exp (-s)) := by
    rw [m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ hZi]
    simp_rw [hangular]
    exact integral_const_mul _ _
  have hinner : rho * Real.exp (-1) ≤ rho :=
    mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num))
  have hshellEq := upperBoundaryShell_integral_eq x hrho.le
    ((A.energy_integrable B hB hei hb).mono_set (upperBoundaryDisk_subset_interior hx hP hr))
  rw [m64UpperBoundaryDisk_eq_annulus hx hP hr,
    m64UpperBoundaryDisk_eq_annulus (hinner.trans_lt hx) (by linarith) (hinner.trans_lt hr)]
    at hshellEq
  change (∫ p in upperBoundaryShell x rho, F p) = A.boundaryDiskEnergy B x rho -
    A.boundaryDiskEnergy B x (rho * Real.exp (-1)) at hshellEq
  rw [hid, hshellEq] at henergy
  exact ⟨hi, by linarith⟩

end PoincareConjecture.M64ObservedWeakAnnulus
