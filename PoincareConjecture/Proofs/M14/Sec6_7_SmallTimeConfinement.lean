import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeConfinementCore
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem exists_smallTime_action_confinement
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (x : G.Point)
    {T δ A C : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcurv : ∀ q : G.Point, G.spacetime.timeFunction q ∈ Icc (T - δ) T →
      horizontalCurvatureNorm G.leafwise q ≤ C)
    {O : Set G.Point} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧ ∀ τ ∈ Ioc 0 τ₀, ∀ y : G.Point,
      ∀ p : M14BackwardPath G T 0 τ x y,
        M14BackwardLAction G p ≤ A * Real.sqrt τ → MapsTo p.curve (Icc 0 τ) O := by
  classical
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := by
    change LocallyCompactSpace {v : EuclideanSpace ℝ (Fin 1) // 0 ≤ v 0}
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin 1) => v 0) := by fun_prop
    exact (isClosed_le continuous_const hc).locallyCompactSpace
  let : LocallyCompactSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin n)))
  let : LocallyCompactSpace G.Point := ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) G.Point
  obtain ⟨b, U, lift, hU, hxU, hlift, hright, hclock⟩ := exists_smooth_gauge_lift G x
  obtain ⟨K, hK, hxK, hKUO⟩ := exists_compact_subset (hU.inter hO) ⟨hxU, hxO⟩
  have hKU : K ⊆ U := fun q hq => (hKUO hq).1
  have hKO : K ⊆ O := fun q hq => (hKUO hq).2
  obtain ⟨κ, hκ, hcoercive⟩ := compact_gauge_metric_coercive b lift hK
    (hlift.continuousOn.mono hKU) (lift x).2
  have hnear : (G.gaugeCover.cylinder b).toSpacetime ⁻¹' interior K ∈ 𝓝 (lift x) :=
    (G.gaugeCover.cylinder b).smooth.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds (by simpa only [hright x hxU] using hxK))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let D : ℝ := 2 * A + 4 * δ * ((n : ℝ) ^ 2 * C)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hD1 : 0 < D + 1 := by linarith
  let τ₀ := min δ (min (ε / 2) (κ * ε ^ 2 / (D + 1)))
  have hτ₀ : 0 < τ₀ := lt_min hδ (lt_min (by positivity) (by positivity))
  refine ⟨τ₀, hτ₀, min_le_left _ _, ?_⟩
  intro τ hτ y p hp
  have hτδ : τ ≤ δ := hτ.2.trans (min_le_left _ _)
  have hτε : τ < ε :=
    (hτ.2.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by linarith)
  have hτbound : τ ≤ κ * ε ^ 2 / (D + 1) :=
    hτ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : D * τ < κ * ε ^ 2 := by
    have hh := (le_div_iff₀ hD1).mp hτbound
    nlinarith [hτ.1]
  have hkin := squarePath_kinetic_energy_le_of_curvature_bound p hM12 hτδ hC hcurv
  simp only [Real.sqrt_zero, sub_zero] at hkin
  have hupper : (∫ s in 0..Real.sqrt τ, pathSquareKinetic p s) ≤
      (2 * A + 4 * τ * ((n : ℝ) ^ 2 * C)) * Real.sqrt τ := by
    calc
      _ ≤ 2 * M14BackwardLAction G p +
          4 * τ * ((n : ℝ) ^ 2 * C) * Real.sqrt τ := hkin
      _ ≤ 2 * (A * Real.sqrt τ) +
          4 * τ * ((n : ℝ) ^ 2 * C) * Real.sqrt τ :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = _ := by ring
  have hcoeff : 2 * A + 4 * τ * ((n : ℝ) ^ 2 * C) ≤ D := by
    dsimp only [D]
    have hh := mul_le_mul_of_nonneg_right hτδ
      (mul_nonneg (sq_nonneg (n : ℝ)) hC)
    nlinarith
  have henergy : Real.sqrt τ * (∫ s in 0..Real.sqrt τ, pathSquareKinetic p s) <
      κ * ε ^ 2 := by
    calc
      _ ≤ Real.sqrt τ * ((2 * A + 4 * τ * ((n : ℝ) ^ 2 * C)) * Real.sqrt τ) :=
        mul_le_mul_of_nonneg_left hupper (Real.sqrt_nonneg τ)
      _ = (2 * A + 4 * τ * ((n : ℝ) ^ 2 * C)) * (Real.sqrt τ) ^ 2 := by ring
      _ = (2 * A + 4 * τ * ((n : ℝ) ^ 2 * C)) * τ := by rw [Real.sq_sqrt hτ.1.le]
      _ ≤ D * τ := mul_le_mul_of_nonneg_right hcoeff hτ.1.le
      _ < κ * ε ^ 2 := hsmall
  have hconf := squarePath_mapsTo_gauge_core_of_energy p b lift hM12 hlift hright hclock
    hKU hK.isClosed hxK hκ.le hε hcoercive hball hτε henergy
  intro t ht
  have hs : Real.sqrt t ∈ Icc 0 (Real.sqrt τ) :=
    ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
  simpa only [Real.sq_sqrt ht.1] using hKO (interior_subset (hconf hs))

end PoincareConjecture.M14
