import PoincareConjecture.Proofs.M11.CylinderTimeCover





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.Proofs.M11.CylinderTimeCover

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {C : Type v} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C] (D : CylinderTimeCover.{u, v, w} F K C)

theorem map_worldline_smooth (x : C) :
    ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞
      (fun t : (smoothInterval K).Point ↦ D.map (t, x)) :=
  D.map_smooth.comp (contMDiff_id.prodMk contMDiff_const)

theorem map_worldline_derivative (t : (smoothInterval K).Point) (x : C) :
    mfderiv (𝓡∂ 1) (spacetimeModel n) (fun s : (smoothInterval K).Point ↦ D.map (s, x)) t
      ((smoothInterval K).positiveTangent t) = F.timeVector (D.map (t, x)) := by
  let := F.chartedSpace
  let := intervalChartedSpace K
  obtain ⟨b, hb⟩ := D.covers t
  let := intervalChartedSpace (D.interval b)
  let r : (smoothInterval (D.interval b)).Point := ⟨t.val, hb⟩
  let j := spacetimeIntervalInclusion (smoothInterval (D.interval b))
    (smoothInterval K) (D.subset b)
  have heq : (fun s ↦ D.map (s, x)) ∘ j =
      (fun s ↦ (D.cylinder b).toSpacetime (s, x)) := funext fun s ↦ D.map_eq b s x
  have hc := mfderiv_comp_apply r
    ((D.map_worldline_smooth x (j r)).mdifferentiableAt (by simp))
    ((smoothInterval_inclusion_smooth (D.interval b) K (D.subset b) r).mdifferentiableAt (by simp))
    ((smoothInterval (D.interval b)).positiveTangent r)
  rw [heq, smoothInterval_inclusion_derivative, (D.cylinder b).worldline_derivative,
    ← D.map_eq b r x] at hc
  exact hc.symm

theorem map_differential_injective (p : (smoothInterval K).Point × C) :
    Function.Injective (mfderiv (spacetimeModel n) (spacetimeModel n) D.map p) := by
  let := F.chartedSpace
  let := intervalChartedSpace K
  obtain ⟨b, hb⟩ := D.covers p.1
  let := intervalChartedSpace (D.interval b)
  let r : (smoothInterval (D.interval b)).Point × C := (⟨p.1.val, hb⟩, p.2)
  let j := Prod.map (spacetimeIntervalInclusion (smoothInterval (D.interval b))
    (smoothInterval K) (D.subset b)) (id : C → C)
  have heq : D.map ∘ j = (D.cylinder b).toSpacetime := funext fun q ↦ D.map_eq b q.1 q.2
  have hjSmooth := (smoothInterval_inclusion_smooth (D.interval b) K (D.subset b)).prodMap
    (contMDiff_id (I := 𝓡 n) (M := C))
  have hc := mfderiv_comp r ((D.map_smooth (j r)).mdifferentiableAt (by simp))
    ((hjSmooth r).mdifferentiableAt (by simp))
  rw [heq] at hc
  have hp : j r = p := Prod.ext (Subtype.ext rfl) rfl
  suffices hi : Function.Injective
      (mfderiv (spacetimeModel n) (spacetimeModel n) D.map (j r)) from hp ▸ hi
  have hi : Function.Injective
      ((mfderiv (spacetimeModel n) (spacetimeModel n) D.map (j r)).comp
        (mfderiv (spacetimeModel n) (spacetimeModel n) j r)) := by
    rw [← hc]
    exact (D.cylinder b).differential_injective r
  have hj := interval_product_differential_surjective (IM := 𝓡 n) K (D.interval b)
    (D.subset b) (D.open_time b) r
  intro v w hvw
  obtain ⟨v', rfl⟩ := hj v
  obtain ⟨w', rfl⟩ := hj w
  exact congrArg (mfderiv (spacetimeModel n) (spacetimeModel n) j r) (hi hvw)

end PoincareConjecture.Proofs.M11.CylinderTimeCover
