import PoincareConjecture.Proofs.M35.CapGeometry.SelectedIntrinsicAnnulusClose
import PoincareConjecture.Proofs.M35.CapGeometry.RadialStaticNeck
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipReflectedExclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace

def RadialAnnulusComparison {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℝ)
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (x : V) (epsilon : ℝ) : Prop :=
  let Q := (E.flow.connection t).scalarCurvature x
  let hQ := E.scalar_pos ht x
  let G := M13.scaleSmoothMetric (E.flow.metric t) Q hQ
  let hrot := scaleSmoothMetric_rotation_invariant (E.rotation_invariant t ht) Q hQ
  let hc := scaleSmoothMetric_complete (E.flow.metric t) (E.complete t ht) Q hQ
  let a := radialArclength G ‖x‖
  0 < a - epsilon⁻¹ ∧ RoundCylinderClose epsilon 0
    (radialCylinderTensor (fun u => intrinsicWarpingRadius G hrot hc (a + u) ^ 2) 1)

noncomputable def RadialAnnulusComparison.staticNeck
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℝ)
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (x : V) (epsilon : ℝ)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) (q : UnitTwoSphere)
    (h : RadialAnnulusComparison E t ht x epsilon) :
    StandardStaticNeck E.atlas (E.flow.metric t) (E.flow.connection t) epsilon := by
  let Q := (E.flow.connection t).scalarCurvature x
  have hQ : 0 < Q := E.scalar_pos ht x
  let G := M13.scaleSmoothMetric (E.flow.metric t) Q hQ
  let a := radialArclength G ‖x‖
  exact radialStaticNeck (E.flow.metric t) (E.rotation_invariant t ht) E.atlas
    (E.flow.connection t) Q hQ (E.complete t ht) q a 1 epsilon zero_lt_one he hehalf
    (by simpa only [one_mul] using h.1)
    (scalar_intrinsic_radial_center (E.flow.metric t) (E.rotation_invariant t ht)
      P (E.flow.connection t) Q hQ (E.complete t ht) q x)
    (by simpa only [one_mul] using h.2)

theorem blowupSequence_radial_annulus_comparison
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → V)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ k in atTop, RadialAnnulusComparison E (t (L.subsequence k)) (ht _)
      (x (L.subsequence k)) epsilon := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  obtain ⟨epsilonBar, hbar, hmodels⟩ := P.kappa_models.theorem_9_93
  obtain ⟨C, _hC, hCmodels⟩ := hmodels (epsilonBar / 2) (by positivity) (by linarith)
  obtain ⟨N⟩ := blowupSequence_far_tip_sphere_line P E t x ht hR hd L A
    (hCmodels A.solution).alternatives
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G (k : ℕ) : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  let a k := radialArclength (G k) ‖x (L.subsequence k)‖
  have hclose := blowupSequence_intrinsic_annulus_eventually_close P E t x ht hR hd L A N
    a (fun _ => 1) 0 epsilon le_rfl he tendsto_const_nhds
    (Eventually.of_forall fun _ => by simp only [a, G, Q, sub_self, abs_zero, le_refl])
  have ha := (blowupSequence_intrinsic_center_limits P E t x ht hR hd L).1
  filter_upwards [hclose, ha.eventually (eventually_gt_atTop epsilon⁻¹)] with k hk hak
  have hpair : 0 < a k - epsilon⁻¹ ∧
      RoundCylinderClose epsilon 0 (radialCylinderTensor
        (fun u => intrinsicWarpingRadius (G k)
          (scaleSmoothMetric_rotation_invariant
            (E.rotation_invariant (t (L.subsequence k)) (ht _)) (Q k) (hQ k))
          (scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
            (E.complete (t (L.subsequence k)) (ht _)) (Q k) (hQ k)) (a k + u) ^ 2) 1) :=
    ⟨sub_pos.mpr hak, by simpa only [one_mul] using hk⟩
  simpa only [RadialAnnulusComparison, a, G, Q, blowupSequence_scale] using hpair

end PoincareConjecture.M35.OrdinaryRealization
