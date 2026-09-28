import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialReplacementEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarCircleColumn







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain

namespace M64ObservedWeakAnnulus



def lowerEnergyDensity (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (p : LoopPlane) : ℝ :=
  (Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 0 p) (A.lowerExtensionColumn 0 p) +
    Q (A.lowerExtensionMap p) (A.lowerExtensionColumn 1 p) (A.lowerExtensionColumn 1 p)) / 2



def lowerTotalEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) : ℝ := ∫ p in O, A.lowerEnergyDensity Q p



def lowerDiskEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (a : LoopPlane) (r : ℝ) : ℝ :=
  ∫ p in ball a r, A.lowerEnergyDensity Q p



def lowerAngularEnergy (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : ℝ :=
  ∫ x in Icc (0 : ℝ) curvePeriod,
    ‖m64MorreyPolarAngularColumn a rho A.lowerExtensionColumn (annulusPoint x s)‖ ^ 2



theorem lower_energy_integrable (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) : IntegrableOn (A.lowerEnergyDensity Q) O volume := by
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  obtain ⟨hu, hV⟩ := A.lower_extension_memLp hc0
  exact m64Observed_energyDensity_integrable Q hQ hb A.lowerExtensionMap
    (hei.aestronglyMeasurable_comp_iff.mp hu.aestronglyMeasurable) A.lowerExtensionColumn hV



theorem lowerEnergyDensity_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ Q q v v)
    (p : LoopPlane) : 0 ≤ A.lowerEnergyDensity Q p :=
  div_nonneg (add_nonneg (hpos _ _) (hpos _ _)) (by norm_num)



theorem lowerTotalEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ Q q v v) :
    0 ≤ A.lowerTotalEnergy Q := integral_nonneg (A.lowerEnergyDensity_nonneg Q hpos)



theorem lowerDiskEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) : 0 ≤ A.lowerDiskEnergy Q a r :=
  integral_nonneg (A.lowerEnergyDensity_nonneg Q hpos)



theorem lowerAngularEnergy_nonneg (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (a : LoopPlane) (rho s : ℝ) : 0 ≤ A.lowerAngularEnergy a rho s :=
  integral_nonneg fun _ => sq_nonneg _



theorem lowerDiskEnergy_le_total (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) (r : ℝ) (hball : ball a r ⊆ O) :
    A.lowerDiskEnergy Q a r ≤ A.lowerTotalEnergy Q :=
  setIntegral_mono_set (A.lower_energy_integrable hc0 Q hQ hei hb)
    (Eventually.of_forall (A.lowerEnergyDensity_nonneg Q hpos))
    (Eventually.of_forall hball)



theorem lowerDiskEnergy_mono (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (hc0 : ContDiff ℝ 1 (e ∘ c0))
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (hpos : ∀ q v, 0 ≤ Q q v v)
    (a : LoopPlane) {r R : ℝ} (hrR : r ≤ R) (hball : ball a R ⊆ O) :
    A.lowerDiskEnergy Q a r ≤ A.lowerDiskEnergy Q a R :=
  setIntegral_mono_set ((A.lower_energy_integrable hc0 Q hQ hei hb).mono_set hball)
    (Eventually.of_forall (A.lowerEnergyDensity_nonneg Q hpos))
    (Eventually.of_forall (ball_subset_ball hrR))

end M64ObservedWeakAnnulus

end PoincareConjecture
