import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.HornBalls

/-!
# Actual terminal necks on compact source closures

Morgan--Tian Claim 11.33, printed p. 288, and Claim 11.35,
printed pp. 289-291. A slightly larger normalized ball lies in the
actual terminal horn and hence supplies a centered original neck at
every point of the smaller ball's closure.

The read-only donor is `DeepHorn.terminalBlowupSequence_baseBalls_subset_horns`
in DeepHorn/Blowup/Horns. Its compiled owned replacement is used here.
The closure calculation is the actual extended-metric calculation in
owned Continuation/Step. Reviewed paper: `claim11_35-positive-seed.md`,
section 2. The supplied horn accuracy is retained without unfolding the
terminal accuracy factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)

/-- Every point of a fixed normalized base-ball closure eventually has
its actual centered terminal horn neck, with the supplied accuracy.
Source: Claims 11.33 and 11.35, printed pp. 288-291. -/
theorem terminalBlowupSequence_eventually_closure_strongNecks
    (hM04 : RicciFlowCurvatureTheory.{u}) {K B : ℝ} {accuracy : ℕ → ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension (accuracy k))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ closure ((terminalBlowupSequence H Q x hpos hdiv).baseBall k A),
        ∃ N : GeneralizedStrongNeck (Q k).extension.extended (T k) (accuracy k),
          N.center = y := by
  let S := terminalBlowupSequence H Q x hpos hdiv
  intro A hA
  filter_upwards [terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv hM04
    hK hB hcutoff hconstant horn hx hboundary (A + 1) (by linarith)] with k hk y hy
  let g := (S.flow k).metric (S.base k).1
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : ((S.flow k).slice (S.base k).1).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : ((S.flow k).slice (S.base k).1).carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace ((S.flow k).slice (S.base k).1).carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) _
  have hsqrt : 0 < Real.sqrt (S.scale k) := Real.sqrt_pos.mpr (S.base_scalar_pos k)
  have hr : 0 < (A + 1) / Real.sqrt (S.scale k) := div_pos (by linarith) hsqrt
  have hclosure : closure (S.baseBall k A) ⊆
      {z | g.edist (S.base k).2 z ≤ ENNReal.ofReal (A / Real.sqrt (S.scale k))} := by
    apply closure_minimal
    · intro z hz
      exact (show g.edist (S.base k).2 z < ENNReal.ofReal (A / Real.sqrt (S.scale k))
        from hz).le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hlarge : y ∈ S.baseBall k (A + 1) :=
    (hclosure hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr
      ((div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)))
  exact (horn k).every_point_neck y (hk hlarge)

end PoincareMT.M32
