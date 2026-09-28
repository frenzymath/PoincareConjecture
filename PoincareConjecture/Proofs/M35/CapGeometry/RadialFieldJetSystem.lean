import PoincareConjecture.Proofs.M35.Mathlib.PointJetBounds
import PoincareConjecture.Proofs.M35.CapGeometry.RadialFieldPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ
local notation "C" => B × ((V →L[ℝ] V →L[ℝ] V) × B)

local instance radialMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance radialMetricNormedSpace : NormedSpace ℝ B := inferInstance
local instance radialGammaNormedGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V) := inferInstance
local instance radialGammaNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V) := inferInstance
local instance radialCoefficientNormedGroup : NormedAddCommGroup C := inferInstance
local instance radialCoefficientNormedSpace : NormedSpace ℝ C := inferInstance
local instance radialSystemNormedGroup : NormedAddCommGroup (C × (V × ℝ)) := inferInstance
local instance radialSystemNormedSpace : NormedSpace ℝ (C × (V × ℝ)) := inferInstance

noncomputable def radialFieldJetPolynomial (z : C × (V × ℝ)) : V →L[ℝ] V × ℝ :=
  let b := z.1.1
  let gamma := z.1.2.1
  let ricci := z.1.2.2
  let u := z.2.1
  let a := z.2.2
  (a • (ContinuousLinearMap.id ℝ V - (b u).smulRight u) - gamma.flip u).prod
    (-(ricci u u / 2 + a ^ 2) • b u)

theorem radialFieldJetPolynomial_contDiff : ContDiff ℝ ∞ radialFieldJetPolynomial := by
  have hu : ContDiff ℝ ∞ (fun z : C × (V × ℝ) => z.2.1) := contDiff_snd.fst
  have ha : ContDiff ℝ ∞ (fun z : C × (V × ℝ) => z.2.2) := contDiff_snd.snd
  have hbu : ContDiff ℝ ∞ (fun z : C × (V × ℝ) => z.1.1 z.2.1) :=
    (contDiff_fst.fst).clm_apply hu
  have hleft : ContDiff ℝ ∞ (fun z : C × (V × ℝ) =>
      z.2.2 • (ContinuousLinearMap.id ℝ V - (z.1.1 z.2.1).smulRight z.2.1) -
        z.1.2.1.flip z.2.1) := by
    have hflip : ContDiff ℝ ∞ (fun z : C × (V × ℝ) => z.1.2.1.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ V V V).contDiff.comp (by fun_prop)
    exact (ha.smul (contDiff_const.sub (hbu.smulRight hu))).sub (hflip.clm_apply hu)
  have hright : ContDiff ℝ ∞ (fun z : C × (V × ℝ) =>
      -(z.1.2.2 z.2.1 z.2.1 / 2 + z.2.2 ^ 2) • z.1.1 z.2.1) := by
    have hr : ContDiff ℝ ∞ (fun z : C × (V × ℝ) => z.1.2.2 z.2.1 z.2.1) :=
      ((contDiff_fst.snd.snd).clm_apply hu).clm_apply hu
    exact ((hr.div_const 2).add (ha.pow 2)).neg.smul hbu
  exact (ContinuousLinearMap.prodₗᵢ ℝ).contDiff.comp (hleft.prodMk hright)

theorem radial_field_shape_jets_at {ι : Type*} {n : ℕ}
    {coeff : ι → V → C} {z : ι → V → V × ℝ} {p : ι → V}
    (hcoeff : ∀ i, ContDiffAt ℝ ∞ (coeff i) (p i))
    (hz : ∀ i, ContDiffAt ℝ ∞ (z i) (p i))
    (hcj : HasUniformJetBoundsAt n coeff p)
    (hzero : ∃ K : ℝ, ∀ i, ‖z i (p i)‖ ≤ K)
    (hEq : ∀ i, fderiv ℝ (z i) =ᶠ[𝓝 (p i)]
      (fun x => radialFieldJetPolynomial (coeff i x, z i x))) :
    HasUniformJetBoundsAt (n + 1) z p := by
  obtain ⟨Kz, hKz⟩ := hzero
  obtain ⟨Kc, hKc⟩ := hcj 0 (Nat.zero_le _)
  have hmap (i : ι) : (coeff i (p i), z i (p i)) ∈
      Metric.closedBall (0 : C × (V × ℝ)) (max Kc Kz) := by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    apply max_le
    · have hc : ‖coeff i (p i)‖ ≤ Kc := by
        simpa only [norm_iteratedFDeriv_zero] using hKc i
      exact hc.trans (le_max_left _ _)
    · exact (hKz i).trans (le_max_right _ _)
  have hj : ∀ m ≤ n + 1, HasUniformJetBoundsAt m z p := by
    intro m
    induction m with
    | zero =>
        intro _ r hr
        have : r = 0 := Nat.eq_zero_of_le_zero hr
        subst r
        exact ⟨Kz, fun i => by simpa only [norm_iteratedFDeriv_zero] using hKz i⟩
    | succ m ih =>
        intro hm
        have hzm := ih (by omega)
        have hpair := (hcj.mono_order (show m ≤ n by omega)).prodMk hzm hcoeff hz
        have hder := hpair.comp_fixed (fun i => (hcoeff i).prodMk (hz i))
          (isCompact_closedBall (0 : C × (V × ℝ)) (max Kc Kz))
          (fun _ _ => radialFieldJetPolynomial_contDiff.contDiffAt) hmap
        exact HasUniformJetBoundsAt.succ_of_fderiv ⟨Kz, hKz⟩
          (hder.congr (fun i => (hEq i).symm))
  exact hj (n + 1) le_rfl

end

end PoincareConjecture.M35
