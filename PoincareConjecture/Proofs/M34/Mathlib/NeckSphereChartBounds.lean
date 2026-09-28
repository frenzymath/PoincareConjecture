import PoincareConjecture.Proofs.M34.Mathlib.SphereChartMetric
import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import PoincareConjecture.Proofs.M34.Mathlib.LinearPrecomposeLocalJets
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_stereoInvFunAux_joint {m : ℕ∞ω} :
    ContDiff ℝ m (fun z : E × E => stereoInvFunAux z.1 z.2) := by
  have hn : ContDiff ℝ m (fun z : E × E => ‖z.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  exact ((hn.add contDiff_const).inv (fun z => by positivity)).smul
    ((contDiff_const.smul contDiff_snd).add ((hn.sub contDiff_const).smul contDiff_fst))

theorem stereoInvFunAux_uniform_spatial_jet_bound [FiniteDimensional ℝ E]
    (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v w : E, ‖v‖ ≤ 1 → ‖w‖ ≤ R →
      ‖iteratedFDeriv ℝ m (stereoInvFunAux v) w‖ ≤ C := by
  have hc := ((contDiff_stereoInvFunAux_joint (E := E) (m := ∞)).contDiffOn
    (s := (univ : Set E) ×ˢ (univ : Set E))).iteratedFDeriv_snd_of_isOpen isOpen_univ m
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : E) 1).prod
    (isCompact_closedBall (0 : E) R)).exists_bound_of_continuousOn
      (hc.continuousOn.mono (fun _ _ => ⟨mem_univ _, mem_univ _⟩))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v w hv hw
  apply (hC (v, w) ?_).trans (le_max_left _ _)
  simpa only [mem_prod, mem_closedBall, dist_zero_right] using And.intro hv hw

theorem sphere_chart_symm_uniform_jet_bound [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (R : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : sphere (0 : E) 1,
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
        ‖iteratedFDeriv ℝ m
          (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := stereoInvFunAux_uniform_spatial_jet_bound (E := E) R m
  refine ⟨C, hC, ?_⟩
  intro q x hx
  let v : sphere (0 : E) 1 := -q
  let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
  let L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] E :=
    (ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp U.symm.toLinearIsometry
  have heq : (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) =
      stereoInvFunAux (v : E) ∘ L := by
    funext y
    change ((stereographic' n v).symm y : E) = stereoInvFunAux (v : E) (L y)
    simpa [stereoInvFunAux, smul_add, L, U] using stereographic'_symm_apply v y
  have hL : ‖L.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simpa only [LinearIsometry.coe_toContinuousLinearMap, L.norm_map, one_mul] using le_refl ‖y‖
  rw [heq]
  apply (L.toContinuousLinearMap.norm_iteratedFDeriv_comp_right_of_contDiffAt
    ((contDiff_stereoInvFunAux (v := (v : E)) (m := ∞)).contDiffAt.of_le
      (by exact_mod_cast le_top))).trans
  have hbase := hb (v : E) (L x) (norm_eq_of_mem_sphere v).le
    ((L.norm_map x).trans_le hx)
  exact (mul_le_mul hbase (pow_le_pow_left₀ (norm_nonneg _) hL m)
    (pow_nonneg (norm_nonneg _) _) hC).trans_eq (by rw [one_pow, mul_one])
