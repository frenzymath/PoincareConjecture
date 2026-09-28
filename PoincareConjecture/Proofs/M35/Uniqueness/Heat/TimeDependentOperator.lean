import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormPerturbedHeat
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure ℝ} {A : ℝ → E →L[ℝ] F} {C : ℝ}

theorem memLp_timeDependent_apply (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (u : Lp E 2 μ) :
    MemLp (fun t => A t (u t)) 2 μ := by
  have hm : AEStronglyMeasurable (fun t => A t (u t)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.memLp u).aestronglyMeasurable)
  apply ((Lp.memLp u).norm.const_mul C).mono' hm
  filter_upwards [hC] with t ht
  exact ((A t).le_opNorm (u t)).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

theorem memLp_timeDependent_fun (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) {u : ℝ → E} (hu : MemLp u 2 μ) :
    MemLp (fun t => A t (u t)) 2 μ := by
  apply (memLp_congr_ae ?_).mp (memLp_timeDependent_apply hA hC (hu.toLp u))
  filter_upwards [hu.coeFn_toLp] with t ht
  rw [ht]

def timeDependentLp (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (u : Lp E 2 μ) : Lp F 2 μ :=
  (memLp_timeDependent_apply hA hC u).toLp (fun t => A t (u t))

theorem timeDependentLp_coe (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (u : Lp E 2 μ) :
    timeDependentLp hA hC u =ᵐ[μ] fun t => A t (u t) :=
  (memLp_timeDependent_apply hA hC u).coeFn_toLp

theorem norm_timeDependentLp_le (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (u : Lp E 2 μ) :
    ‖timeDependentLp hA hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [timeDependentLp_coe hA hC u, hC] with t ht hCt
  rw [ht]
  exact ((A t).le_opNorm (u t)).trans (mul_le_mul_of_nonneg_right hCt (norm_nonneg _))

def timeDependentLpLinearMap (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := timeDependentLp hA hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [timeDependentLp_coe hA hC (u + v),
      timeDependentLp_coe hA hC u, timeDependentLp_coe hA hC v,
      Lp.coeFn_add u v, Lp.coeFn_add (timeDependentLp hA hC u) (timeDependentLp hA hC v)]
      with t huv hu hv hs ht
    simp only [huv, ht, hs, Pi.add_apply, hu, hv, map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [timeDependentLp_coe hA hC (c • u), timeDependentLp_coe hA hC u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (timeDependentLp hA hC u)] with t hcu hu hs ht
    simp only [RingHom.id_apply, hcu, ht, hs, Pi.smul_apply, hu, map_smul]


def timeDependentLpOperator (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (timeDependentLpLinearMap hA hC).mkContinuous C (norm_timeDependentLp_le hA hC)

theorem timeDependentLpOperator_coe (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (u : Lp E 2 μ) :
    timeDependentLpOperator hA hC u =ᵐ[μ] fun t => A t (u t) :=
  timeDependentLp_coe hA hC u

theorem norm_timeDependentLpOperator_le (hA : AEStronglyMeasurable A μ)
    (hC : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖timeDependentLpOperator hA hC‖ ≤ C :=
  (timeDependentLpLinearMap hA hC).mkContinuous_norm_le hC0 _

end PoincareConjecture.M35.Uniqueness.Heat
