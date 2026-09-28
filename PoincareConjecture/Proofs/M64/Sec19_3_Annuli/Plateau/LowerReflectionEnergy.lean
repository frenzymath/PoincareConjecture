import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "R" => m60PlaneReflection
local notation "T" => m64AnnulusRadialFlip
local notation "v" => m64AnnulusRadialTranslation



theorem m64AnnulusRadialFlip_lower_translation (p : LoopPlane) : T (v + p) = R p := by
  ext i
  fin_cases i <;> simp [m64AnnulusRadialFlip_apply, m64AnnulusRadialTranslation,
    m60PlaneReflection_apply, annulusPoint]

private theorem reflected_norm_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : LoopPlane → E) {epsilon : ℝ} (he : ‖epsilon‖ = 1)
    {p : LoopPlane} (hp : p ∈ O) (hface : p 1 ≠ 0) :
    ‖m64AnnulusLowerExtend (fun z => epsilon • V (T z)) V p‖ ^ 2 =
      ‖(S).indicator V p‖ ^ 2 + ‖(S).indicator V (R p)‖ ^ 2 := by
  classical
  by_cases hneg : p 1 < 0
  · have hpnot : p ∉ S := fun h => lt_asymm hneg
      ((m64AnnulusInterior_coordinates p).mp h).2.2.1
    have hRp : R p ∈ S := by
      apply (m64AnnulusInterior_coordinates _).mpr
      simpa only [m60PlaneReflection_apply, ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        using And.intro hp.1 (And.intro hp.2.1
          (And.intro (neg_pos.mpr hneg) (by linarith [hp.2.2.1] : -p 1 < 1)))
    simp only [m64AnnulusLowerExtend, if_pos hneg, m64AnnulusRadialFlip_lower_translation,
      indicator_of_notMem hpnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      indicator_of_mem hRp, norm_smul, he, one_mul]
  · have hpos : 0 < p 1 := lt_of_le_of_ne (le_of_not_gt hneg) hface.symm
    have hpS : p ∈ S := (m64AnnulusInterior_coordinates p).mpr
      ⟨hp.1, hp.2.1, hpos, hp.2.2.2⟩
    have hRpnot : R p ∉ S := by
      intro hh
      have h := ((m64AnnulusInterior_coordinates _).mp hh).2.2.1
      simp only [m60PlaneReflection_apply, if_neg (by decide : (1 : Fin 2) ≠ 0)] at h
      linarith
    simp only [m64AnnulusLowerExtend, if_neg hneg, indicator_of_mem hpS,
      indicator_of_notMem hRpnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]




theorem m64LowerReflection_integral_norm_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : LoopPlane → E} (hV : MemLp V 2 (volume.restrict S))
    {epsilon : ℝ} (he : ‖epsilon‖ = 1) {b : LoopPlane} {r : ℝ}
    (hball : closedBall b r ⊆ O) :
    (∫ p in closedBall b r,
      ‖m64AnnulusLowerExtend (fun z => epsilon • V (T z)) V p‖ ^ 2) =
      (∫ p in closedBall b r ∩ S, ‖V p‖ ^ 2) +
        ∫ p in closedBall (R b) r ∩ S, ‖V p‖ ^ 2 := by
  classical
  let U := (S).indicator V
  have hU := (memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr hV
  have hi : Integrable (fun p => ‖U p‖ ^ 2) volume := hU.norm.integrable_sq
  have hir : Integrable (fun p => ‖U (R p)‖ ^ 2) volume :=
    m60PlaneReflection.measurePreserving.integrable_comp_of_integrable hi
  have hface : ∀ᵐ p : LoopPlane ∂volume, p 1 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_radial_line_null 0
  have hpoint : (fun p => ‖m64AnnulusLowerExtend (fun z => epsilon • V (T z)) V p‖ ^ 2)
      =ᵐ[volume.restrict (closedBall b r)] (fun p => ‖U p‖ ^ 2 + ‖U (R p)‖ ^ 2) := by
    filter_upwards [ae_restrict_of_ae hface, ae_restrict_mem measurableSet_closedBall] with p hn hp
    exact reflected_norm_sq V he (hball hp) hn
  have hpre : R ⁻¹' closedBall (R b) r = closedBall b r := by
    ext p
    change dist (R p) (R b) ≤ r ↔ dist p b ≤ r
    rw [LinearIsometryEquiv.dist_map]
  have hindicator (z : LoopPlane) : (∫ p in closedBall z r, ‖U p‖ ^ 2) =
      ∫ p in closedBall z r ∩ S, ‖V p‖ ^ 2 := by
    have heq : (fun p => ‖U p‖ ^ 2) = (S).indicator (fun p => ‖V p‖ ^ 2) := by
      funext p
      by_cases hp : p ∈ S <;> simp [U, hp]
    rw [heq, setIntegral_indicator isOpen_interior.measurableSet]
  rw [integral_congr_ae hpoint, integral_add hi.integrableOn hir.integrableOn, hindicator]
  congr 1
  calc
    _ = ∫ p in closedBall (R b) r, ‖U p‖ ^ 2 := by
      rw [← hpre]
      exact m60PlaneReflection.measurePreserving.setIntegral_preimage_emb
        m60PlaneReflection.toHomeomorph.measurableEmbedding
        (fun p => ‖U p‖ ^ 2) (closedBall (R b) r)
    _ = _ := hindicator _

end PoincareConjecture
