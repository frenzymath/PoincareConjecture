import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider

/-! Adapted from Mapher `PoincareMT/Definitions/M15Noncollapsing.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral

universe u

namespace PoincareMT

/-! ### Compact Theorem 8.10 data -/

/-!
The compact input uses one supplied ordinary Ricci flow on the exact closed
interval `Icc 0 T`.  `t₀` is valid in that interval and the tested curvature
bound is on the complete closed backward cylinder.  The initial unit-ball
bound, full initial curvature bound, and constants `omega,T₀` are independent
of the generalized configuration interface.
-/
structure M15CompactTheorem810Data
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (T : ℝ) (F : RicciFlow 3 M (Set.Icc 0 T))
    (omega T₀ : ℝ) where
  T_pos : 0 < T
  T_le_T₀ : T ≤ T₀
  omega_pos : 0 < omega
  T₀_pos : 0 < T₀
  initial_curvature_bound : ∀ q : M,
    |(F.connection 0).curvatureTensorNorm q| ≤ 1
  initial_unit_ball_volume : ∀ q : M,
    ENNReal.ofReal omega ≤
      calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q 1)
  t₀ : ℝ
  t₀_mem : t₀ ∈ Set.Icc 0 T
  t₀_nonneg : 0 ≤ t₀
  t₀_le_T : t₀ ≤ T
  p : M
  r : ℝ
  radius_pos : 0 < r
  radius_sq_le_t₀ : r ^ 2 ≤ t₀
  time_window : Set.Icc (t₀ - r ^ 2) t₀ ⊆ Set.Icc 0 T
  curvature_bound : ∀ s ∈ Set.Icc (t₀ - r ^ 2) t₀,
    ∀ q ∈ (F.metric t₀).ball p r,
      |(F.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2

def M15CompactTheorem810Estimate
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {T : ℝ} {F : RicciFlow 3 M (Set.Icc 0 T)} {omega T₀ : ℝ}
    (D : M15CompactTheorem810Data M T F omega T₀) (κ : ℝ) : Prop :=
  ENNReal.ofReal (κ * D.r ^ 3) ≤
    calibratedMetricVolume (F.metric D.t₀)
      ((F.metric D.t₀).ball D.p D.r)

/-!
The compact conclusion places `kappa_c` before the compact manifold, flow,
time, point, and radius.  It is a separate clause of M15 and does not smuggle
Theorem 8.1's `taubar,l₀,V` into Theorem 8.10.
-/
structure M15CompactUniformData (omega T₀ : ℝ) where
  omega_pos : 0 < omega
  T₀_pos : 0 < T₀
  kappa : ℝ
  kappa_pos : 0 < kappa
  estimate : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T3Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M]
    (T : ℝ) (F : RicciFlow 3 M (Set.Icc 0 T)),
    (D : M15CompactTheorem810Data M T F omega T₀) →
      M15CompactTheorem810Estimate D kappa

def M15CompactTheorem810 : Prop :=
  ∀ (omega T₀ : ℝ), 0 < omega → 0 < T₀ →
    Nonempty (M15CompactUniformData.{u} omega T₀)

/-!
The combined M15 data keeps the generalized and compact clauses distinct.
This is a packaging interface for the one later proving theorem; its fields
are propositions and it has no construction or admission here.
-/
structure M15NoncollapsingTheory (n : ℕ) : Prop where
  generalized : M15GeneralizedUniformTheorem.{u} n
  compact : M15CompactTheorem810.{u}

end PoincareMT
