import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamRadialCut
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPullbackTest

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "v" => m64AnnulusSeamTranslation

theorem m64_exists_compact_radial_seam_test
    {K : Set LoopPlane} (hK : IsCompact K) (hKO : K ⊆ m64AnnulusSeamDomain)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    ∃ psi Z : LoopPlane → ℝ,
      MemLp psi 2 volume ∧ MemLp Z 2 volume ∧ HasCompactSupport psi ∧
      HasWeakPartialDeriv (1 : Fin 2) Z psi univ ∧
      ∀ p ∈ K, psi p = m64AnnulusSeamExtend phi p ∧
        Z p = m64AnnulusSeamExtend
          (fun q => fderiv ℝ phi q (EuclideanSpace.single (1 : Fin 2) 1)) p := by
  classical
  obtain ⟨delta, eta, hdelta, -, heta, hetac, -, hone, -⟩ :=
    Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hK m64AnnulusSeamDomain_isOpen hKO
  let left := fun p : LoopPlane => eta p * phi (v + p)
  let right := fun p : LoopPlane => eta p * phi p
  let D := fun (f : LoopPlane → ℝ) p =>
    fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)
  let psi := m64AnnulusAngularCut.piecewise left right
  let Z := m64AnnulusAngularCut.piecewise (D left) (D right)
  have hleft : ContDiff ℝ 1 left :=
    (heta.of_le (by simp)).mul (hp.comp (contDiff_const.add contDiff_id))
  have hright : ContDiff ℝ 1 right := (heta.of_le (by simp)).mul hp
  have hlc : HasCompactSupport left := hetac.mul_right
  have hrc : HasCompactSupport right := hetac.mul_right
  have hlM : MemLp left 2 volume := hleft.continuous.memLp_of_hasCompactSupport hlc
  have hrM : MemLp right 2 volume := hright.continuous.memLp_of_hasCompactSupport hrc
  have hDlM : MemLp (D left) 2 volume :=
    ((hleft.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hlc.fderiv_apply ℝ _)
  have hDrM : MemLp (D right) 2 volume :=
    ((hright.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hrc.fderiv_apply ℝ _)
  have hpsiM : MemLp psi 2 volume := MemLp.piecewise m64AnnulusAngularCut_measurable
    (hlM.mono_measure Measure.restrict_le_self) (hrM.mono_measure Measure.restrict_le_self)
  have hZM : MemLp Z 2 volume := MemLp.piecewise m64AnnulusAngularCut_measurable
    (hDlM.mono_measure Measure.restrict_le_self) (hDrM.mono_measure Measure.restrict_le_self)
  have hpsiC : HasCompactSupport psi := by
    apply HasCompactSupport.intro' (K := tsupport eta) hetac (isClosed_tsupport eta)
    intro p hpeta
    have hz : eta p = 0 := image_eq_zero_of_notMem_tsupport hpeta
    simp only [psi, piecewise, left, right, hz, zero_mul, ite_self]
  have hw : HasWeakPartialDeriv (1 : Fin 2) Z psi univ :=
    m64WeakPartial_radial_angular_piecewise hlM hrM hDlM hDrM
      (HasWeakPartialDeriv.of_contDiff isOpen_univ hleft)
      (HasWeakPartialDeriv.of_contDiff isOpen_univ hright)
  refine ⟨psi, Z, hpsiM, hZM, hpsiC, hw, ?_⟩
  intro p hpK
  have hetanear : eta =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds p hdelta] with q hq
    exact hone q (Metric.mem_cthickening_of_dist_le q p delta K hpK
      (Metric.mem_ball.mp hq).le)
  have hlnear : left =ᶠ[𝓝 p] (fun q => phi (v + q)) := by
    filter_upwards [hetanear] with q hq
    simp only [left, hq, one_mul]
  have hrnear : right =ᶠ[𝓝 p] phi := by
    filter_upwards [hetanear] with q hq
    simp only [right, hq, one_mul]
  have hDl : D left p = fderiv ℝ phi (v + p) (EuclideanSpace.single (1 : Fin 2) 1) := by
    dsimp only [D]
    rw [hlnear.fderiv_eq, m64Scalar_fderiv_translation hp]
  have hDr : D right p = fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) := by
    dsimp only [D]
    rw [hrnear.fderiv_eq]
  by_cases hneg : p 0 < 0
  · have hc : p ∈ m64AnnulusAngularCut := hneg
    simp only [psi, Z, piecewise_eq_of_mem _ _ _ hc,
      m64AnnulusSeamExtend, if_pos hneg, hlnear.eq_of_nhds, hDl, and_self]
  · have hc : p ∉ m64AnnulusAngularCut := hneg
    simp only [psi, Z, piecewise_eq_of_notMem _ _ _ hc,
      m64AnnulusSeamExtend, if_neg hneg, hrnear.eq_of_nhds, hDr, and_self]

end PoincareConjecture
