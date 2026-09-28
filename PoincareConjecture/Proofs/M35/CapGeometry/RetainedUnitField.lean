import PoincareConjecture.Proofs.M35.CapGeometry.SelectedBallImage
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipUnitField










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness



theorem blowupSequence_far_tip_radial_field_on_limit_ball
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (r ε : ℝ) (hε : 0 < ε) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G : RiemannianMetric 3 StandardCapSpace :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let D := M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k))) Q hQ
      let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      ∀ z ∈ (L.limit.flow.metric 0).ball L.limit.base r,
        phi z ≠ 0 ∧ G.inner (phi z) (radialUnitField G (phi z))
          (radialUnitField G (phi z)) = 1 ∧
        ∀ w : StandardCapSpace,
          G.inner (phi z) (D.connection (radialUnitField G) (phi z) w)
            (D.connection (radialUnitField G) (phi z) w) ≤
              ε ^ 2 * G.inner (phi z) w w := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have hsource := E.normalized_radial_field_almost_parallel_on_balls
    P t x ht hd (2 * r) ε hε
  have hsub := L.subsequence_strictMono.tendsto_atTop.eventually hsource
  filter_upwards [hsub, blowupSequence_image_ball_bounded P E t x ht hR L r]
    with k hk hball
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  let D := M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k))) Q hQ
  let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  change ∀ z ∈ (L.limit.flow.metric 0).ball L.limit.base r,
    phi z ≠ 0 ∧ G.inner (phi z) (radialUnitField G (phi z))
      (radialUnitField G (phi z)) = 1 ∧
    ∀ w : StandardCapSpace,
      G.inner (phi z) (D.connection (radialUnitField G) (phi z) w)
        (D.connection (radialUnitField G) (phi z) w) ≤ ε ^ 2 * G.inner (phi z) w w
  intro z hz
  have hmem := hball ⟨z, hz, rfl⟩
  simp only [blowupSequence_scale] at hmem
  simpa only [G, D, Q, M13.scaleLeviCivitaData_connection, blowupSequence_scale]
    using hk (phi z) hmem

end PoincareConjecture.M35.OrdinaryRealization
