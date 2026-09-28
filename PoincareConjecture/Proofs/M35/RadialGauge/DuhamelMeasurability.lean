import PoincareConjecture.Proofs.M35.RadialGauge.SlabSourceExtension










set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem heatDuhamel_stronglyMeasurable {f : ℝ → V → F}
    (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (Function.uncurry (heatDuhamel f)) := by
  have hkernel : StronglyMeasurable (fun q : ((ℝ × V) × ℝ) × V =>
      f q.1.2 (q.1.1.2 + Real.sqrt (2 * (q.1.1.1 - q.1.2)) • q.2)) :=
    hf.comp_measurable (g := fun q : ((ℝ × V) × ℝ) × V =>
      (q.1.2, q.1.1.2 + Real.sqrt (2 * (q.1.1.1 - q.1.2)) • q.2)) (by fun_prop)
  let H (q : (ℝ × V) × ℝ) : F := heatAverage (q.1.1 - q.2) (f q.2) q.1.2
  have hH : StronglyMeasurable H := hkernel.integral_prod_right'
  let S : Set ((ℝ × V) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ q.1.1}
  let R : Set ((ℝ × V) × ℝ) := {q | q.1.1 < q.2 ∧ q.2 ≤ 0}
  have hS : MeasurableSet S := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hR : MeasurableSet R := by
    exact (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hforward := (hH.indicator hS).integral_prod_right' (ν := volume)
  have hbackward := (hH.indicator hR).integral_prod_right' (ν := volume)
  convert hforward.sub hbackward using 1
  funext p
  have hforward_eq : (fun s => S.indicator H (p, s)) =
      (Ioc (0 : ℝ) p.1).indicator (fun s => heatAverage (p.1 - s) (f s) p.2) := by
    funext s
    rfl
  have hbackward_eq : (fun s => R.indicator H (p, s)) =
      (Ioc p.1 (0 : ℝ)).indicator (fun s => heatAverage (p.1 - s) (f s) p.2) := by
    funext s
    rfl
  simp only [Pi.sub_apply]
  rw [hforward_eq, hbackward_eq, integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc]
  rfl

end PoincareConjecture.M35.RadialGauge
