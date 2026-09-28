import PoincareConjecture.Proofs.M35.CapGeometry.SelectedIntrinsicCollar
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicAnnulusClose










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace



theorem blowupSequence_intrinsic_annulus_eventually_close
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (_N : M27SphereLineFlowCertificate A.solution),
      let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G (k : ℕ) : RiemannianMetric 3 V :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
      let hrot k := scaleSmoothMetric_rotation_invariant
        (E.rotation_invariant (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
      let hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
        (E.complete (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
      let a k := radialArclength (G k) ‖x (L.subsequence k)‖
      ∀ (c b : ℕ → ℝ) (length epsilon : ℝ), 0 ≤ length → 0 < epsilon →
        Tendsto b atTop (𝓝 1) → (∀ᶠ k in atTop, |c k - a k| ≤ length) →
        ∀ᶠ k in atTop, RoundCylinderClose epsilon 0
          (radialCylinderTensor
            (fun u => intrinsicWarpingRadius (G k) (hrot k) (hc k)
              (c k + b k * u) ^ 2) (b k)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N
  dsimp only
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G (k : ℕ) : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  have hrot k := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
  have hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
    (E.complete (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
  let a k := radialArclength (G k) ‖x (L.subsequence k)‖
  intro c b length epsilon hlength hepsilon hb hshift
  apply intrinsic_annulus_eventually_close G hrot hc c b hepsilon hb
  intro idx hidx s hs
  have hb2 : ∀ᶠ k in atTop, |b k| < 2 :=
    hb.abs.eventually (eventually_lt_nhds (by norm_num : |(1 : ℝ)| < 2))
  apply blowupSequence_intrinsic_collar_profile_jets P E t x ht hR hd L A N idx hidx
    (fun k => c (idx k) + b (idx k) * s k) (length + 2 * epsilon⁻¹) (by positivity)
  filter_upwards [hidx.eventually hshift, hidx.eventually hb2] with k hck hbk
  have hsk : |s k| ≤ epsilon⁻¹ := abs_le.mpr (hs k)
  calc
    |c (idx k) + b (idx k) * s k - a (idx k)| =
        |(c (idx k) - a (idx k)) + b (idx k) * s k| := by ring_nf
    _ ≤ |c (idx k) - a (idx k)| + |b (idx k) * s k| := abs_add_le _ _
    _ ≤ length + 2 * epsilon⁻¹ := by
      rw [abs_mul]
      exact add_le_add hck (mul_le_mul hbk.le hsk (abs_nonneg _) (by norm_num))

end PoincareConjecture.M35.OrdinaryRealization
