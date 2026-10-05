import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.BlowupSubsequence
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.ControlledCylinders

/-!
# A terminal limit bound gives common short controls

Morgan--Tian Theorem 11.1, p. 271, after Claim 11.7: compact source-ball
coverage and uniform scalar convergence transfer the limit bound to every
fixed source ball on the selected sequence. A unit of slack is added before
the spatial radius is chosen. The resulting bound supplies one short slab.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The retained terminal maps and compact scalar convergence transfer a
global limit bound to radius-independent short controls on the selected
sequence (Theorem 11.1, p. 271). Source-ball coverage is required in the
reverse direction, on one fixed compact limit set for each radius. -/
theorem shortControls_of_terminal_scalar_convergence
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (C : FlowCarrier.{v} 3) (g : RiemannianMetric 3 C.carrier)
    (D : LeviCivitaData g)
    (e : ∀ k, C.carrier → ((S.flow (phi k)).slice (S.base (phi k)).1).carrier)
    (hcapture : ∀ A : ℝ, 0 < A → ∃ K : Set C.carrier, IsCompact K ∧
      ∀ᶠ k : ℕ in atTop, S.baseBall (phi k) A ⊆ e k '' K)
    (hscalar : ∀ K : Set C.carrier, IsCompact K → TendstoUniformlyOn
      (fun k x => (S.flow (phi k)).scalar ⟨(S.base (phi k)).1, e k x⟩ /
        S.scale (phi k)) D.scalarCurvature atTop K)
    {B : ℝ} (hbound : ∀ x : C.carrier, D.scalarCurvature x ≤ B) :
    Nonempty (ShortControlledBlowupHypotheses
      (reindexedBlowupSequence S phi hphi) kappa r₀) := by
  apply shortControlledBlowupHypotheses_of_terminal_scalar_bound hC
    (reindexedCommonBlowupControls H phi hphi)
    (D := max 4 (B + 1)) (le_max_left _ _)
  intro A hA
  obtain ⟨K, hK, hcover⟩ := hcapture A hA
  have hclose := Metric.tendstoUniformlyOn_iff.mp (hscalar K hK) 1 zero_lt_one
  filter_upwards [hcover, hclose] with k hkcover hkclose
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hkcover hx
  have herror : |D.scalarCurvature y -
      (S.flow (phi k)).scalar ⟨(S.base (phi k)).1, e k y⟩ / S.scale (phi k)| < 1 := by
    simpa only [Real.dist_eq] using hkclose y hy
  have hnormalized :
      (S.flow (phi k)).scalar ⟨(S.base (phi k)).1, e k y⟩ / S.scale (phi k) ≤ B + 1 := by
    have := (abs_lt.mp herror).1
    linarith [hbound y]
  exact (div_le_iff₀ (S.base_scalar_pos (phi k))).mp
    (hnormalized.trans (le_max_right _ _))

end PoincareMT.M30
