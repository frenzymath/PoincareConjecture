import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusTraceAverages
import PoincareConjecture.Proofs.M64.Mathlib.InteriorCurveTraces
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "sigma" => volume.restrict (Icc (0 : ℝ) 1)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

local instance : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne





theorem interiorCurve_vertical_trace_pointwise
    {f d : LoopPlane → ℝ} {b0 b1 : ℝ → ℝ}
    (hf : Integrable f mu) (hd2 : MemLp d 2 mu)
    (hfs : ContDiffOn ℝ 1 f S)
    (hdeq : d =ᵐ[mu] (fun p => fderiv ℝ f p e1))
    (havg0 : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + (s - 1) * d (annulusPoint x s)) = b0 x)
    (havg1 : ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + s * d (annulusPoint x s)) = b1 x) :
    ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b0 x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t) ∧
      b1 x - f (annulusPoint x s) = ∫ t in s..(1 : ℝ), d (annulusPoint x t) := by
  have hdsq : Integrable (fun p => d p ^ 2) mu := by
    simpa only [Real.norm_eq_abs, sq_abs] using hd2.norm.integrable_sq
  have hd : Integrable d mu := hd2.integrable (by norm_num)
  have hprodD := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hdsq
  have hprodD1 := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hd
  have hprodF := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf
  have heqprod := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae hdeq
  have heqfib := Measure.ae_ae_of_ae_prod heqprod
  have hinter : ∀ᵐ x ∂nu, x ∈ Ioo (0 : ℝ) curvePeriod := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [havg0, havg1, heqfib, hprodD1.prod_right_ae,
    hprodD.prod_right_ae, hinter] with x hx0 hx1 hxe hdi hdi2 hxinter
  have hdi' : IntegrableOn (fun t => d (annulusPoint x t))
      (Icc (0 : ℝ) 1) volume := by
    change IntegrableOn (fun t => d (annulusPoint x t)) (Icc (0 : ℝ) 1) volume at hdi
    exact hdi
  have hdi2' : IntegrableOn (fun t => d (annulusPoint x t) ^ 2)
      (Icc (0 : ℝ) 1) volume := by
    change IntegrableOn (fun t => d (annulusPoint x t) ^ 2) (Icc (0 : ℝ) 1) volume at hdi2
    exact hdi2
  have hxe' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      d (annulusPoint x t) =
        fderiv ℝ f (annulusPoint x t) e1 := by
    simpa only [Function.comp_apply] using hxe
  have hdfi : IntegrableOn (fun t => fderiv ℝ f (annulusPoint x t) e1)
      (Icc (0 : ℝ) 1) volume := hdi'.congr hxe'
  have hdfi2 : IntegrableOn (fun t => (fderiv ℝ f (annulusPoint x t) e1) ^ 2)
      (Icc (0 : ℝ) 1) volume := by
    apply hdi2'.congr
    filter_upwards [hxe'] with t ht
    rw [ht]
  have hdx : IntervalIntegrable (fun t => fderiv ℝ f (annulusPoint x t) e1)
      volume 0 1 := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hdfi
  have hder (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s => f (annulusPoint x s))
        (fderiv ℝ f (annulusPoint x t) e1) t := by
    have hp : annulusPoint x t ∈ S :=
      (m64AnnulusInterior_coordinates _).mpr ⟨hxinter.1, hxinter.2, ht.1, ht.2⟩
    have hc := (hfs.contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt (by simp)
    have hcomp := hc.hasFDerivAt.comp_hasDerivAt t
      (m64AnnulusPoint_vertical_hasDerivAt x t)
    exact hcomp
  have havg0' : (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + (s - 1) * fderiv ℝ f (annulusPoint x s) e1) = b0 x := by
    calc
      _ = ∫ s in Icc (0 : ℝ) 1,
          f (annulusPoint x s) + (s - 1) * d (annulusPoint x s) := by
            apply integral_congr_ae
            filter_upwards [hxe'] with s hs
            rw [hs]
      _ = b0 x := hx0
  have havg1' : (∫ s in Icc (0 : ℝ) 1,
      f (annulusPoint x s) + s * fderiv ℝ f (annulusPoint x s) e1) = b1 x := by
    calc
      _ = ∫ s in Icc (0 : ℝ) 1,
          f (annulusPoint x s) + s * d (annulusPoint x s) := by
            apply integral_congr_ae
            filter_upwards [hxe'] with s hs
            rw [hs]
      _ = b1 x := hx1
  obtain ⟨F, hF, hFeq, hFformula, hF0, hF1⟩ :=
    interiorCurve_unit_trace_averages hder hdx
  have hF0b : F 0 = b0 x := hF0.symm.trans havg0'
  have hF1b : F 1 = b1 x := hF1.symm.trans havg1'
  intro s hs
  have hfs := hFeq hs
  have hfs' : F s = f (annulusPoint x s) := by simpa using hfs
  have hleft : f (annulusPoint x s) - b0 x =
      ∫ t in (0 : ℝ)..s, d (annulusPoint x t) := by
    have hprim := hFformula s
    rw [hfs', hF0b] at hprim
    have hsub_left : uIoc (0 : ℝ) s ⊆ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hs.1.le]
      exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hs.2.le)
    have hxeI : ∀ᵐ t ∂volume.restrict (uIoc (0 : ℝ) s),
        d (annulusPoint x t) = fderiv ℝ f (annulusPoint x t) e1 :=
      ae_restrict_of_ae_restrict_of_subset hsub_left hxe'
    have hi := intervalIntegral.integral_congr_ae_restrict hxeI
    rw [← hi] at hprim
    linarith [hprim]
  have hright : b1 x - f (annulusPoint x s) =
      ∫ t in s..(1 : ℝ), d (annulusPoint x t) := by
    have hleftI : IntervalIntegrable (fun t => fderiv ℝ f (annulusPoint x t) e1)
        volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1.le).mpr
        (hdfi.mono_set (Icc_subset_Icc le_rfl hs.2.le))
    have hrightI : IntervalIntegrable (fun t => fderiv ℝ f (annulusPoint x t) e1)
        volume s 1 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs.2.le).mpr
        (hdfi.mono_set (Icc_subset_Icc hs.1.le le_rfl))
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleftI hrightI
    have hfull' : ∫ t in (0 : ℝ)..1,
        fderiv ℝ f (annulusPoint x t) e1 = b1 x - b0 x := by
      linarith [hFformula 1, hF1b, hF0b]
    rw [hfull'] at hadd
    have hxeI : ∀ᵐ t ∂volume.restrict (uIoc s (1 : ℝ)),
        d (annulusPoint x t) = fderiv ℝ f (annulusPoint x t) e1 :=
      ae_restrict_of_ae_restrict_of_subset
        (by
          rw [uIoc_of_le hs.2.le]
          exact Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1.le le_rfl)) hxe'
    have hi := intervalIntegral.integral_congr_ae_restrict hxeI
    rw [← hi] at hadd
    have hprim := hFformula s
    rw [hfs', hF0b] at hprim
    linarith
  constructor
  · exact hleft
  · exact hright

end PoincareConjecture
