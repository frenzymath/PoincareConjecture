import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalDynamics
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.TimeSegments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative ValueInitial

theorem measurePreserving_add_time (S T : ℝ) :
    MeasurePreserving (fun t : ℝ => S + t) (timeMeasure T)
      (volume.restrict (Ioc S (S + T))) := by
  have hp : (fun t : ℝ => S + t) ⁻¹' Ioc S (S + T) = Ioc 0 T := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro ht <;> constructor <;> linarith only [ht.1, ht.2]
  simpa only [hp] using (measurePreserving_add_left volume S).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc S (S + T)))

theorem memLp_add_time_restrict {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {S T B : ℝ} (hS : 0 ≤ S) (hST : S + T ≤ B)
    (hf : MemLp f 2 (timeMeasure B)) :
    MemLp (fun t => f (S + t)) 2 (timeMeasure T) :=
  (hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc hS hST) le_rfl)).comp_measurePreserving
    (measurePreserving_add_time S T)

theorem ae_add_time_restrict {P : ℝ → Prop} {S T B : ℝ}
    (hS : 0 ≤ S) (hST : S + T ≤ B) (hP : ∀ᵐ t ∂timeMeasure B, P t) :
    ∀ᵐ t ∂timeMeasure T, P (S + t) :=
  (measurePreserving_add_time S T).quasiMeasurePreserving.ae
    (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hS hST) hP)

theorem integral_equation_time_restrict {f q : ℝ → ℝ} {S T B : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S + T ≤ B)
    (hf : IntegrableOn f (Ioc 0 B) volume)
    (heq : ∀ t ∈ Icc 0 B, q t = q 0 + ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Icc 0 T, q (S + t) = q S + ∫ s in (0 : ℝ)..t, f (S + s) := by
  intro t ht
  have hSB : S ≤ B := by linarith only [hST, hT]
  have hStB : S + t ≤ B := by linarith only [ht.2, hST]
  have hfi0 : IntervalIntegrable f volume 0 S :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).mpr
      (hf.mono_set (Ioc_subset_Ioc le_rfl hSB))
  have hfit : IntervalIntegrable f volume S (S + t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_add_of_nonneg_right ht.1)).mpr
      (hf.mono_set (Ioc_subset_Ioc hS hStB))
  have hsum := intervalIntegral.integral_add_adjacent_intervals hfi0 hfit
  have h0 := heq S ⟨hS, hSB⟩
  have h1 := heq (S + t) ⟨add_nonneg hS ht.1, hStB⟩
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  linarith only [h0, h1, hsum]

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem principalValueHeat_restrict (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r S T B : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S + T ≤ B)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A (r + t))) (Icc 0 B))
    (hLc : ContinuousOn (fun t => L (r + t)) (Icc 0 B))
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hsol : PrincipalValueHeat K A L r B u₀ v U) :
    PrincipalValueHeat K (fun t => A (r + S + t)) (fun t => L (r + S + t)) 0 T
      (U S) (fun t => v (S + t)) (fun t => U (S + t)) := by
  have hshift : MapsTo (fun t : ℝ => S + t) (Icc 0 T) (Icc 0 B) := by
    intro t ht
    constructor <;> linarith only [hS, ht.1, ht.2, hST]
  have hPs : ContinuousOn (fun t => principalFormOperator K (A (r + S + (0 + t))))
      (Icc 0 T) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, add_assoc] using
      hAc.comp (continuous_const.add continuous_id).continuousOn hshift
  have hLs : ContinuousOn (fun t => L (r + S + (0 + t))) (Icc 0 T) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, add_assoc] using
      hLc.comp (continuous_const.add continuous_id).continuousOn hshift
  apply principalValueHeat_of_integral K (fun t => A (r + S + t))
    (fun t => L (r + S + t)) (r := 0) (v := fun t => v (S + t))
    (U := fun t => U (S + t)) hT hPs hLs
    (memLp_add_time_restrict hS hST hsol.1) (by rw [add_zero])
    (hsol.2.2.1.comp (continuous_const.add continuous_id).continuousOn hshift)
    (ae_add_time_restrict hS hST hsol.2.2.2.1)
  intro t ht w
  let f : ℝ → ℝ := fun s =>
    inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L (r + s) (v s)) -
      principalVectorEnergy K (A (r + s)) w (v s)
  have hf : IntegrableOn f (Ioc 0 B) volume :=
    (principalHeat_integrand_memLp K A L hAc hLc hsol.1 w).integrable (by norm_num)
  have heq : ∀ s ∈ Icc 0 B,
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U s) =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U 0) +
          ∫ z in (0 : ℝ)..s, f z := by
    simpa only [hsol.2.1] using fun s hs => hsol.2.2.2.2.2 s hs w
  simpa only [f, zero_add, add_assoc] using
    integral_equation_time_restrict hS hT hST hf heq t ht

end PoincareConjecture.M35.Uniqueness.Heat
