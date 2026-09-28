import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RawAnnulusObservedLTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

theorem m64Lower_continuous_trace {m : ℕ}
    {f d U : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {b : ℝ → EuclideanSpace ℝ (Fin m)} {O : Set LoopPlane}
    (hO : IsOpen O) (hsub : O ⊆ m64AnnulusLowerDomain)
    (hU : ContinuousOn U O) (hf : ContinuousOn f S) (hb : Continuous b)
    (hae : U =ᵐ[volume.restrict (O ∩ S)] f) (hd : IntegrableOn d S)
    (hpoint : ∀ᵐ x ∂nu, ∀ s ∈ Ioo (0 : ℝ) 1,
      f (annulusPoint x s) - b x = ∫ t in (0 : ℝ)..s, d (annulusPoint x t)) :
    ∀ x, annulusPoint x 0 ∈ O → U (annulusPoint x 0) = b x := by
  have hline : Continuous (fun x : ℝ => annulusPoint x 0) := by
    have h : ContDiff ℝ 1 (fun x : ℝ => annulusPoint x 0) := by
      apply contDiff_euclidean.mpr
      intro i
      fin_cases i
      · exact contDiff_id
      · exact contDiff_const
    exact h.continuous
  have hvertical (x : ℝ) : Continuous (fun s : ℝ => annulusPoint x s) := by
    have h : ContDiff ℝ 1 (fun s : ℝ => annulusPoint x s) := by
      apply contDiff_euclidean.mpr
      intro i
      fin_cases i
      · exact contDiff_const
      · exact contDiff_id
    exact h.continuous
  let J := (fun x : ℝ => annulusPoint x 0) ⁻¹' O
  have hJ : IsOpen J := hO.preimage hline
  have hJsub : J ⊆ Icc (0 : ℝ) curvePeriod := by
    intro x hx
    have hp := hsub hx
    exact ⟨hp.1.le, hp.2.1.le⟩
  have heq : EqOn U f (O ∩ S) := Measure.eqOn_open_of_ae_eq hae
    (hO.inter isOpen_interior) (hU.mono inter_subset_left) (hf.mono inter_subset_right)
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hd
  have hdx : ∀ᵐ x ∂nu, IntegrableOn (fun t => d (annulusPoint x t))
      (Icc (0 : ℝ) 1) volume := by
    simpa only [Function.comp_apply, IntegrableOn] using hprod.prod_right_ae
  have hboundary : (fun x => U (annulusPoint x 0)) =ᵐ[volume.restrict J] b := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJsub hpoint,
      ae_restrict_of_ae_restrict_of_subset hJsub hdx,
      ae_restrict_mem hJ.measurableSet] with x hx hxi hxJ
    have hxO : annulusPoint x 0 ∈ O := hxJ
    have hxcoords := hsub hxO
    have hxlim : Tendsto (fun s : ℝ => U (annulusPoint x s) - b x)
        (𝓝[>] (0 : ℝ)) (𝓝 (U (annulusPoint x 0) - b x)) :=
      (((hU.continuousAt (hO.mem_nhds hxO)).comp (hvertical x).continuousAt).sub
        continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    have hprim : ContinuousOn (fun s => ∫ t in (0 : ℝ)..s, d (annulusPoint x t))
        (Icc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn (fun t => d (annulusPoint x t)) (uIcc (0 : ℝ) 1) from by
          simpa only [uIcc_of_le zero_le_one] using hxi)
    have hright : Tendsto (fun s : ℝ => s) (𝓝[>] (0 : ℝ)) (𝓝[Icc (0 : ℝ) 1] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds,
        Filter.Eventually.mono (Ioo_mem_nhdsGT zero_lt_one) fun _ hs => ⟨hs.1.le, hs.2.le⟩⟩
    have hzero : Tendsto (fun s => ∫ t in (0 : ℝ)..s, d (annulusPoint x t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [intervalIntegral.integral_same, Function.comp_def] using
        (hprim 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp hright
    have hstay : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), annulusPoint x s ∈ O :=
      ((hvertical x).tendsto 0).eventually (hO.mem_nhds hxO) |>.filter_mono
        nhdsWithin_le_nhds
    have hsame : (fun s => U (annulusPoint x s) - b x) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun s => ∫ t in (0 : ℝ)..s, d (annulusPoint x t)) := by
      filter_upwards [hstay, Ioo_mem_nhdsGT zero_lt_one] with s hsO hs
      have hpS : annulusPoint x s ∈ S := (m64AnnulusInterior_coordinates _).mpr
        ⟨hxcoords.1, hxcoords.2.1, hs.1, hs.2⟩
      rw [heq ⟨hsO, hpS⟩]
      exact hx s hs
    exact sub_eq_zero.mp (tendsto_nhds_unique hxlim (hzero.congr' hsame.symm))
  exact Measure.eqOn_open_of_ae_eq hboundary hJ
    (hU.comp hline.continuousOn (fun _ hx => hx)) hb.continuousOn

end PoincareConjecture
