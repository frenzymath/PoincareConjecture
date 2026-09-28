import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Flux
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.Exponential.Lipschitz

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

include he hei

theorem normalized_exp_neg_heat_pairing_nonpos
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hconv : Convex ℝ (closure O))
    {α β : ℝ} (hα : 0 < α)
    (hCD : closure O ×ˢ Icc α β ⊆ domain J e)
    {u : Spacetime n → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u (closure O ×ˢ Icc α β))
    (hslice : ∀ᵐ τ ∂volume.restrict (Ioo α β),
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, (F.metric (-τ)).pullbackVolumeDensity e x * Real.exp (-u (x, τ)) *
        ((-deriv (fun s => u (x, s)) τ + (F.connection (-τ)).scalarCurvature (e x) -
          (n : ℝ) / (2 * τ)) * ψ x -
          fderiv ℝ ψ x (((F.metric (-τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ (fun y => u (y, τ)) x)))) ≤ 0)
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ O ×ˢ Ioo α β)
    (hφ0 : ∀ z, 0 ≤ φ z) :
    let v := fun z : Spacetime n => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z)
    let B := fun z => density F e z * v z * (-Canonical.timeDeriv φ z -
      (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1))
    IntegrableOn B (O ×ˢ Ioo α β) ∧ (∫ z in O ×ˢ Ioo α β, B z) ≤ 0 := by
  let U := O ×ˢ Ioo α β
  let C := closure O ×ˢ Icc α β
  let v := fun z : Spacetime n => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-u z)
  let A := fun z => Canonical.timeDeriv (fun y => density F e y * v y) z * φ z +
    ∑ i, Canonical.spatialDeriv i v z *
      ∑ j, weightedPrincipal F e i j z * Canonical.spatialDeriv j φ z
  let B := fun (τ : ℝ) x => (F.metric (-τ)).pullbackVolumeDensity e x *
    Real.exp (-u (x, τ)) *
      ((-deriv (fun s => u (x, s)) τ + (F.connection (-τ)).scalarCurvature (e x) -
        (n : ℝ) / (2 * τ)) * φ (x, τ) -
        fderiv ℝ (fun y => φ (y, τ)) x
          (((F.metric (-τ)).pullbackCoefficients e x).inverse
            (fderiv ℝ (fun y => u (y, τ)) x)))
  have hUC : U ⊆ C := fun z hz => ⟨subset_closure hz.1, hz.2.1.le, hz.2.2.le⟩
  have hU : IsOpen U := hO.prod isOpen_Ioo
  obtain ⟨Cu, Cw, hv, hw⟩ := exists_lipschitzOnWith_normalized_exp_neg F e he hei
    (hOc.prod isCompact_Icc) (hconv.prod (convex_Icc α β)) hCD
    (fun z hz => hα.trans_le hz.2.1) hu
  obtain ⟨hAi, hpair, hEq⟩ := integral_heat_flux_eq_coordinate_pairing F e he hei
    hU (hUC.trans hCD) (hv.mono hUC) (hw.mono hUC) hφ hφc hφU
  have hAprod : Integrable A
      ((volume.restrict O).prod (volume.restrict (Ioo α β))) := by
    rw [Measure.prod_restrict]
    exact hAi.integrableOn
  have heq : A =ᵐ[(volume.restrict O).prod (volume.restrict (Ioo α β))]
      (fun z => z.2 ^ (-(n : ℝ) / 2) * B z.2 z.1) := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem hU.measurableSet,
      ae_restrict_of_ae (Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn
        volume hU (hu.mono hUC))] with z hz hdu
    exact normalized_exp_neg_heatFlux_eq F e he hei (hdu hz)
      (hφ.differentiable (by simp) z) (hCD (hUC hz)) (hα.trans hz.2.1)
  have heqtime := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq)
  have hzero : ∀ z ∉ U, A z = 0 := by
    intro z hz
    have hzφ : z ∉ tsupport φ := fun h => hz (hφU h)
    have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hzφ
    have hdφ (i : Fin n) : Canonical.spatialDeriv i φ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hzφ (tsupport_fderiv_apply_subset ℝ (Canonical.spatialDirection i) h))
    simp only [A, hφz, hdφ, mul_zero, Finset.sum_const_zero, zero_add]
  refine ⟨hpair, ?_⟩
  rw [← hEq]
  change (∫ z, A z) ≤ 0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  change (∫ z in O ×ˢ Ioo α β, A z
    ∂(volume : Measure (Euclid n)).prod (volume : Measure ℝ)) ≤ 0
  rw [← Measure.prod_restrict, integral_prod_symm A hAprod]
  apply integral_nonpos_of_ae
  filter_upwards [heqtime, hslice, ae_restrict_mem measurableSet_Ioo] with τ heqτ hsτ hτ
  have hψ : ContDiff ℝ ∞ (fun x => φ (x, τ)) :=
    hφ.comp (contDiff_id.prodMk contDiff_const)
  have hψsupport : tsupport (fun x => φ (x, τ)) ⊆ O := by
    intro x hx
    exact (hφU (tsupport_comp_subset_preimage
      (f := fun x : Euclid n => (x, τ)) φ (by fun_prop) hx)).1
  have hψc : HasCompactSupport (fun x => φ (x, τ)) :=
    (hφc.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) (by
      intro x hx
      exact ⟨(x, τ), tsupport_comp_subset_preimage
        (f := fun x : Euclid n => (x, τ)) φ (by fun_prop) hx, rfl⟩)
  change (fun x => A (x, τ)) =ᵐ[volume.restrict O]
    (fun x => τ ^ (-(n : ℝ) / 2) * B τ x) at heqτ
  change (∫ x in O, A (x, τ)) ≤ (0 : ℝ)
  rw [integral_congr_ae heqτ, integral_const_mul]
  exact mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_nonneg (hα.trans hτ.1).le _)
      (hsτ _ hψ hψc hψsupport (fun x => hφ0 (x, τ)))

end PoincareConjecture.RicciFlow.BackwardCoordinates
