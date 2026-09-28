import PoincareConjecture.Proofs.M45.Sec15_1_GluingSupport.NativeJetConvergence
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_BilinearPullback
import PoincareConjecture.Proofs.M45.Ch9_Models.EvolvingCylinderScalar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open M36 M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Z" => cylinderHeightCovector.smulRight cylinderHeightCovector

def neckCoefficientPullback (phi : E → E) (A : E → MetricCoefficient 3) :
    E → MetricCoefficient 3 := fun x =>
  (A (phi x)).bilinearComp (fderiv ℝ phi x) (fderiv ℝ phi x)

theorem contDiffAt_neckCoefficientPullback {phi : E → E} {A : E → MetricCoefficient 3}
    {x : E} (hA : ContDiffAt ℝ ∞ A (phi x)) (hphi : ContDiffAt ℝ ∞ phi x) :
    ContDiffAt ℝ ∞ (neckCoefficientPullback phi A) x := by
  have hc := hA.comp x hphi
  have hd := hphi.fderiv_right (m := ∞) (by simp)
  have hf : ContDiff ℝ ∞ (fun B : MetricCoefficient 3 => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  unfold neckCoefficientPullback ContinuousLinearMap.bilinearComp
  exact hf.contDiffAt.comp x
    ((hf.contDiffAt.comp x (hc.clm_comp hd)).clm_comp hd)

theorem PointJetsConverge.ricci_cylinder_error {ι : Type*} {l : Filter ι}
    {A : ι → E → MetricCoefficient 3} {s0 : ℝ} (hs0 : s0 < 1)
    (h : PointJetsConverge A (fun _ => 0) (evolvingCylinderModelField s0) 0 l)
    (hs : ∀ i, ContDiffAt ℝ ∞ (A i) 0) (hi : ∀ i, (A i 0).IsInvertible) :
    PointJetsVanish (fun i x => jetRicciBilinear (SpacetimeBounds.metricTwoJet (A i) x) -
      (1 / 2 : ℝ) • (cylinderModelField x - Z)) (fun _ => 0) l := by
  let R : E → MetricCoefficient 3 := fun x => (1 / 2 : ℝ) • (cylinderModelField x - Z)
  have hR : ContDiff ℝ ∞ R :=
    (cylinderModelField_contDiff.sub contDiff_const).const_smul _
  have he : jetRicciBilinear ∘ SpacetimeBounds.metricTwoJet (evolvingCylinderModelField s0) = R :=
    funext (model_evolvingCylinder_ricciBilinear hs0)
  have hconv := h.ricci hs (evolvingCylinderModelField_contDiff s0).contDiffAt hi
    (model_evolvingCylinderField_isInvertible hs0 0)
  rw [he] at hconv
  exact hconv.sub_vanish (fun _ => tendsto_const_nhds)
    (fun i => (contDiffAt_jetRicciBilinear (hi i)).comp 0 (contDiffAt_metricTwoJet (hs i)))
    (fun _ => hR.contDiffAt)

set_option maxHeartbeats 800000 in

theorem affine_neck_gluing_error_vanish {ι : Type*} {l : Filter ι}
    {A C D : ι → E → MetricCoefficient 3} {phi : ι → E → E}
    {r s t tau : ι → ℝ} {s0 : ℝ} (hs0 : s0 < 1)
    (hAs : ∀ i, ContDiffAt ℝ ∞ (A i) 0) (hCs : ∀ i, ContDiffAt ℝ ∞ (C i) 0)
    (hDs : ∀ i, ContDiffAt ℝ ∞ (D i) 0) (hphis : ∀ i, ContDiffAt ℝ ∞ (phi i) 0)
    (hphi0 : ∀ i, phi i 0 = 0)
    (hAi : ∀ i, (A i 0).IsInvertible) (hCi : ∀ i, (C i 0).IsInvertible)
    (hA : PointJetsConverge A (fun _ => 0) (evolvingCylinderModelField s0) 0 l)
    (hC : PointJetsConverge C (fun _ => 0) (evolvingCylinderModelField 0) 0 l)
    (hE : PointJetsVanish (fun i x => A i x - evolvingCylinderModelField (s i) x)
      (fun _ => 0) l)
    (hH : PointJetsVanish (fun i x => C i x - evolvingCylinderModelField 0 x)
      (fun _ => 0) l)
    (hK : PointJetsVanish (fun i x => D i x - evolvingCylinderModelField (tau i) x)
      (fun _ => 0) l)
    (hphi : ∀ m, FinitePointJetBounded m phi (fun _ => 0) l)
    (hr : l.IsBoundedUnder (· ≤ ·) (fun i => ‖r i‖))
    (hts : l.IsBoundedUnder (· ≤ ·) (fun i => ‖t i - s i‖))
    (htau : ∀ i, r i * tau i = t i - s i)
    (hmetric : ∀ i, A i =ᶠ[𝓝 (0 : E)]
      fun x => r i • neckCoefficientPullback (phi i) (C i) x)
    (hRicci : ∀ i, (fun x => jetRicciBilinear (metricTwoJet (A i) x)) =ᶠ[𝓝 (0 : E)]
      neckCoefficientPullback (phi i) (fun x => jetRicciBilinear (metricTwoJet (C i) x))) :
    PointJetsVanish (fun i x => r i • neckCoefficientPullback (phi i) (D i) x -
      evolvingCylinderModelField (t i) x) (fun _ => 0) l := by
  let R : E → MetricCoefficient 3 := fun x => (1 / 2 : ℝ) • (cylinderModelField x - Z)
  let S : E → MetricCoefficient 3 := fun x => Z - cylinderModelField x
  let RA := fun i x => jetRicciBilinear (metricTwoJet (A i) x)
  let RC := fun i x => jetRicciBilinear (metricTwoJet (C i) x)
  have hRs : ContDiff ℝ ∞ R :=
    (cylinderModelField_contDiff.sub contDiff_const).const_smul _
  have hSs : ContDiff ℝ ∞ S := contDiff_const.sub cylinderModelField_contDiff
  have hRAs (i : ι) : ContDiffAt ℝ ∞ (RA i) 0 :=
    (contDiffAt_jetRicciBilinear (hAi i)).comp 0 (contDiffAt_metricTwoJet (hAs i))
  have hRCs (i : ι) : ContDiffAt ℝ ∞ (RC i) 0 :=
    (contDiffAt_jetRicciBilinear (hCi i)).comp 0 (contDiffAt_metricTwoJet (hCs i))
  have hpull {F : ι → E → MetricCoefficient 3}
      (hF : PointJetsVanish F (fun _ => 0) l)
      (hFs : ∀ i, ContDiffAt ℝ ∞ (F i) 0) :
      PointJetsVanish (fun i => neckCoefficientPullback (phi i) (F i)) (fun _ => 0) l := by
    apply PointJetsVanish.bilinear_pullback ?_ hphi ?_ hphis
    · simpa only [hphi0] using hF
    · intro i
      simpa only [hphi0] using hFs i
  have hpulls {F : E → MetricCoefficient 3} (i : ι) (hF : ContDiffAt ℝ ∞ F 0) :
      ContDiffAt ℝ ∞ (neckCoefficientPullback (phi i) F) 0 :=
    contDiffAt_neckCoefficientPullback (by simpa only [hphi0] using hF) (hphis i)
  have hRA : PointJetsVanish (fun i x => RA i x - R x) (fun _ => 0) l :=
    hA.ricci_cylinder_error hs0 hAs hAi
  have hRC : PointJetsVanish (fun i x => RC i x - R x) (fun _ => 0) l :=
    hC.ricci_cylinder_error (by norm_num) hCs hCi
  have hRCp := hpull hRC (fun i => (hRCs i).sub hRs.contDiffAt)
  have hdiff := hRCp.sub hRA
    (fun i => hpulls i ((hRCs i).sub hRs.contDiffAt))
    (fun i => (hRAs i).sub hRs.contDiffAt)
  have hdiffs (i : ι) := (hpulls i ((hRCs i).sub hRs.contDiffAt)).sub
    ((hRAs i).sub hRs.contDiffAt)
  have htwo : l.IsBoundedUnder (· ≤ ·) (fun _ : ι => ‖(2 : ℝ)‖) :=
    tendsto_const_nhds.isBoundedUnder_le
  have hS : PointJetsVanish (fun i x => neckCoefficientPullback (phi i) S x - S x)
      (fun _ => 0) l := by
    apply (hdiff.smul htwo hdiffs).congr
    intro i
    filter_upwards [hRicci i] with x hx
    ext v w
    have he := congrArg (fun B : MetricCoefficient 3 => B v w) hx
    simp only [neckCoefficientPullback, ContinuousLinearMap.bilinearComp_apply,
      sub_apply, smul_apply, smul_eq_mul, RA, RC, R, S] at he ⊢
    linear_combination -2 * he
  have hSerrs (i : ι) := (hpulls i hSs.contDiffAt).sub hSs.contDiffAt
  have hEp (i : ι) := (hAs i).sub (evolvingCylinderModelField_contDiff (s i)).contDiffAt
  have hHp (i : ι) := (hCs i).sub (evolvingCylinderModelField_contDiff 0).contDiffAt
  have hKp (i : ι) := (hDs i).sub (evolvingCylinderModelField_contDiff (tau i)).contDiffAt
  have hRH := (hpull hH hHp).smul hr (fun i => hpulls i (hHp i))
  have hRK := (hpull hK hKp).smul hr (fun i => hpulls i (hKp i))
  have hST := hS.smul hts hSerrs
  have hfirst := hE.sub hRH hEp (fun i => (hpulls i (hHp i)).const_smul (r i))
  have hseconds (i : ι) := ((hEp i).sub ((hpulls i (hHp i)).const_smul (r i))).add
    ((hpulls i (hKp i)).const_smul (r i))
  have hsecond := hfirst.add hRK
    (fun i => (hEp i).sub ((hpulls i (hHp i)).const_smul (r i)))
    (fun i => (hpulls i (hKp i)).const_smul (r i))
  apply (hsecond.add hST hseconds (fun i => (hSerrs i).const_smul (t i - s i))).congr
  intro i
  filter_upwards [hmetric i] with x hx
  ext v w
  have he := congrArg (fun B : MetricCoefficient 3 => B v w) hx
  simp only [neckCoefficientPullback, ContinuousLinearMap.bilinearComp_apply,
    evolvingCylinderModelField, sub_apply, add_apply, smul_apply, smul_eq_mul, S] at he ⊢
  linear_combination he +
    (cylinderModelField (phi i x) (fderiv ℝ (phi i) x v) (fderiv ℝ (phi i) x w) -
      Z (fderiv ℝ (phi i) x v) (fderiv ℝ (phi i) x w)) * htau i

end PoincareConjecture.M45
