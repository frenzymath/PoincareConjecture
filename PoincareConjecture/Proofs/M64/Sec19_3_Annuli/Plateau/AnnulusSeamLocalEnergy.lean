import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamLocalComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarCircleColumn







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusSeamDomain



def seamEnergyDensity (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (p : LoopPlane) : ℝ :=
  (Q (m64AnnulusSeamExtend A.map p)
    (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
    (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
  Q (m64AnnulusSeamExtend A.map p)
    (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
    (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2



def seamDiskEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (a : LoopPlane) (r : ℝ) : ℝ :=
  ∫ p in Metric.ball a r, A.seamEnergyDensity Q p



def seamAngularEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) curvePeriod,
    ‖m64MorreyPolarAngularColumn a rho
      (fun i => m64AnnulusSeamExtend (A.column i : LoopPlane → E)) (annulusPoint x s)‖ ^ 2



theorem seamEnergyDensity_eq_extend (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) :
    A.seamEnergyDensity Q = m64AnnulusSeamExtend
      (fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
        Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) := by
  funext p
  simp only [seamEnergyDensity, m64AnnulusSeamExtend]
  split_ifs <;> rfl



theorem seamEnergyDensity_integrable (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) : IntegrableOn (A.seamEnergyDensity Q) O volume := by
  rw [A.seamEnergyDensity_eq_extend Q]
  exact memLp_one_iff_integrable.mp (m64AnnulusSeamExtend_memLp
    (memLp_one_iff_integrable.mpr (A.energy_integrable Q hQ hei hb)))



theorem seamEnergyDensity_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q w, 0 ≤ Q q w w) (p : LoopPlane) :
    0 ≤ A.seamEnergyDensity Q p :=
  div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)



theorem seamDiskEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q w, 0 ≤ Q q w w)
    (a : LoopPlane) (r : ℝ) : 0 ≤ A.seamDiskEnergy Q a r :=
  integral_nonneg (A.seamEnergyDensity_nonneg Q hpos)



theorem seamAngularEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : 0 ≤ A.seamAngularEnergy a rho s :=
  integral_nonneg fun _ => sq_nonneg _



theorem seamDiskEnergy_le_energy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q w, 0 ≤ Q q w w)
    (a : LoopPlane) (r : ℝ) (hball : Metric.ball a r ⊆ O) :
    A.seamDiskEnergy Q a r ≤ 2 * A.energy Q := by
  calc
    _ ≤ ∫ p in O, A.seamEnergyDensity Q p :=
      setIntegral_mono_set (A.seamEnergyDensity_integrable Q hQ hei hb)
        (Eventually.of_forall (A.seamEnergyDensity_nonneg Q hpos))
        (Eventually.of_forall hball)
    _ = _ := A.seam_extension_energy Q hQ hei hb



theorem seamDiskEnergy_mono (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q w, 0 ≤ Q q w w)
    (a : LoopPlane) {r R : ℝ} (hrR : r ≤ R) (hball : Metric.ball a R ⊆ O) :
    A.seamDiskEnergy Q a r ≤ A.seamDiskEnergy Q a R :=
  setIntegral_mono_set ((A.seamEnergyDensity_integrable Q hQ hei hb).mono_set hball)
    (Eventually.of_forall (A.seamEnergyDensity_nonneg Q hpos))
    (Eventually.of_forall (Metric.ball_subset_ball hrR))

end PoincareConjecture.M64ObservedWeakAnnulus
