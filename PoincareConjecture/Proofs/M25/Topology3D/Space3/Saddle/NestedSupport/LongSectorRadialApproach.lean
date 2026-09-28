import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import Mathlib.Tactic












set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in




theorem exists_saddle_nested_shared_radial_exterior_approach
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (inner : Fin 2) (d : ℝ) (hd : 0 < d) (hdUpper : 1 + d < 2)
    (D : Fin 4 → BallNeighborhoodChart E2 E2)
    (c : Fin 4 → UnitCircle → E2)
    (F Delta : Set E2)
    (hBoundary : ∀ i, (D i).boundary = range (c i))
    (hProtect : ∀ i, (D i).closedRegion ∩ F ⊆ Delta)
    (hEndpoint : kappa (J2.symm (0, raisedReturnSign inner)) ∈ F \ Delta)
    (hAvoid : ∀ t ∈ Ioc (0 : ℝ) d, ∀ i,
      kappa (J2.symm (0, raisedReturnSign inner * (1 + d - t))) ∉
        range (c i)) :
    ∃ path : ℝ → E2,
      path = (fun t => kappa (J2.symm
        (0, raisedReturnSign inner * (1 + d - t)))) ∧
      ContinuousOn path (Ioc (0 : ℝ) d) ∧
      IsPreconnected (path '' Ioc (0 : ℝ) d) ∧
      path d ∈ F \ Delta ∧
      (∀ i, Disjoint (path '' Ioc (0 : ℝ) d) (D i).boundary) ∧
      (∀ i, path '' Ioc (0 : ℝ) d ⊆ (D i).closedRegionᶜ) := by
  let radial : ℝ → E2 := fun t =>
    J2.symm (0, raisedReturnSign inner * (1 + d - t))
  let path : ℝ → E2 := fun t => kappa (radial t)
  have hnorm (x y : ℝ) : ‖J2.symm (x, y)‖ ^ 2 = x ^ 2 + y ^ 2 := by
    simpa only [J2.apply_symm_apply] using (hJ2 (J2.symm (x, y))).symm
  have hsign : raisedReturnSign inner ^ 2 = 1 :=
    raisedReturnSign_sq inner
  have hradialNorm (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) d) :
      ‖radial t‖ = 1 + d - t := by
    have hR : 0 ≤ 1 + d - t := by linarith [ht.2]
    have hn := hnorm 0 (raisedReturnSign inner * (1 + d - t))
    change ‖radial t‖ ^ 2 = _ at hn
    rw [zero_pow (by norm_num : 2 ≠ 0), zero_add, mul_pow, hsign, one_mul] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) hR).mp hn
  have hsource (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) d) :
      radial t ∈ kappa.source := by
    apply hkappaSource
    rw [mem_closedBall_zero_iff, hradialNorm t ht]
    linarith [ht.1, ht.2]
  have hradialContinuous : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hpathContinuous : ContinuousOn path (Ioc (0 : ℝ) d) := by
    simpa only [path, Function.comp_def] using
      kappa.continuousOn.comp hradialContinuous.continuousOn hsource
  have hpre : IsPreconnected (path '' Ioc (0 : ℝ) d) :=
    isPreconnected_Ioc.image path hpathContinuous
  have hendpoint : path d ∈ F \ Delta := by
    have heq : radial d = J2.symm (0, raisedReturnSign inner) := by
      dsimp [radial]
      congr 2
      ring
    simpa only [path, heq] using hEndpoint
  have hdisjoint (i : Fin 4) :
      Disjoint (path '' Ioc (0 : ℝ) d) (D i).boundary := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ hy
    rw [hBoundary i] at hy
    exact hAvoid t ht i hy
  have houtside (i : Fin 4) :
      path '' Ioc (0 : ℝ) d ⊆ (D i).closedRegionᶜ := by
    rcases (D i).preconnected_subset_inside_or_outside hpre (hdisjoint i) with hi | ho
    · exfalso
      have hdmem : d ∈ Ioc (0 : ℝ) d := ⟨hd, le_rfl⟩
      have hpinside : path d ∈ (D i).inside := hi ⟨d, hdmem, rfl⟩
      have hpclosed : path d ∈ (D i).closedRegion := by
        rw [← (D i).inside_union_boundary]
        exact Or.inl hpinside
      exact hendpoint.2 (hProtect i ⟨hpclosed, hendpoint.1⟩)
    · exact ho
  refine ⟨path, rfl, hpathContinuous, hpre, hendpoint, hdisjoint, houtside⟩

end PoincareConjecture.M25.Topology3D
