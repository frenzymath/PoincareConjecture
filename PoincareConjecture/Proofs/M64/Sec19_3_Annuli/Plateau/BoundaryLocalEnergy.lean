import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryPolarColumns
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakLocalEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseEnergy










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain




theorem m64UpperBoundaryDisk_eq_annulus {x r : ℝ}
    (hx : r < x) (hP : x + r < curvePeriod) (hr : r < 1) :
    M64.upperBoundaryDisk x r = closedBall (annulusPoint x 0) r ∩ S := by
  apply Subset.antisymm
  · intro p hp
    exact ⟨hp.1, M64.upperBoundaryDisk_subset_interior hx hP hr hp⟩
  · intro p hp
    exact ⟨hp.1, ((m64AnnulusInterior_coordinates p).mp hp.2).2.2.1⟩

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)

namespace M64ObservedWeakAnnulus




def boundaryDiskEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (x r : ℝ) : ℝ :=
  ∫ p in closedBall (annulusPoint x 0) r ∩ S,
    (B (A.map p) (A.column 0 p) (A.column 0 p) +
      B (A.map p) (A.column 1 p) (A.column 1 p)) / 2




def boundaryAngularEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (x r : ℝ) : ℝ :=
  ∫ theta in Icc (0 : ℝ) Real.pi,
    ‖M64.boundaryAngularColumn x r (fun i p => A.column i p) theta‖ ^ 2




theorem boundaryDiskEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ B q v v) (x r : ℝ) :
    0 ≤ A.boundaryDiskEnergy B x r :=
  integral_nonneg (fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num))




theorem boundaryDiskEnergy_mono (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    (x : ℝ) : Monotone (A.boundaryDiskEnergy B x) := by
  intro r R hrR
  exact setIntegral_mono_set ((A.energy_integrable B hB hei hb).mono_set inter_subset_right)
    (ae_of_all _ (fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)))
    (ae_of_all _ (inter_subset_inter_left _ (closedBall_subset_closedBall hrR)))




theorem boundaryDiskEnergy_le_energy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v) (x r : ℝ) :
    A.boundaryDiskEnergy B x r ≤ A.energy B :=
  setIntegral_mono_set (A.energy_integrable B hB hei hb)
    (ae_of_all _ (fun p => div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)))
    (ae_of_all _ inter_subset_right)




theorem column_boundaryDisk_energy_le (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) (x r : ℝ) (i : Fin 2) :
    (∫ p in closedBall (annulusPoint x 0) r ∩ S, ‖A.column i p‖ ^ 2) ≤
      2 * C * A.boundaryDiskEnergy B x r := by
  have hEi := (A.energy_integrable B hB hei hb).mono_set
    (show closedBall (annulusPoint x 0) r ∩ S ⊆ S from inter_subset_right)
  have hcolI : IntegrableOn (fun p => ‖A.column i p‖ ^ 2) S :=
    (Lp.memLp (A.column i)).norm.integrable_sq
  unfold boundaryDiskEnergy
  rw [← integral_const_mul]
  apply integral_mono_ae (hcolI.mono_set inter_subset_right) (hEi.const_mul _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show closedBall (annulusPoint x 0) r ∩ S ⊆ S from inter_subset_right) (A.tangent i)] with p hp
  have hc := hcoercive (A.map p) (A.column i p) hp
  have h0 := mul_nonneg hC (hpos (A.map p) (A.column 0 p))
  have h1 := mul_nonneg hC (hpos (A.map p) (A.column 1 p))
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hc ⊢ <;> nlinarith

end M64ObservedWeakAnnulus

end PoincareConjecture
