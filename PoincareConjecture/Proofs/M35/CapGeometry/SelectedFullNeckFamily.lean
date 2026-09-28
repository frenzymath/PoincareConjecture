import PoincareConjecture.Proofs.M35.CapGeometry.UniformFullNeckJets
import PoincareConjecture.Proofs.M35.CapGeometry.FullNeckJetDifference
import PoincareConjecture.Proofs.M35.Thm12_28.NeckStrictMargin
import PoincareConjecture.Proofs.M35.Thm12_28.NeckPullbackSmoothness

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_full_neck_family_close
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (N : EpsilonNeck (L.limit.flow.metric 0)) (_he : N.epsilon ≤ 1 / 24)
      (_hcompact : IsCompact (closure N.carrier))
      (j : ℕ) (_hstage : closure N.carrier ⊆ L.exhaustion.space j)
      (I J : Set ℝ) (_hJ : IsCompact J) (_hJt : J ⊆ Iic 0) (_hIJ : I ⊆ J)
      (_hclose : RoundCylinderFamilyClose N.epsilon I
        (fun u => roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map)),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      ∀ᶠ k in atTop, RoundCylinderFamilyClose N.epsilon I
        (fun u z v w => Q k *
          roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
            (F k ∘ N.coordinate_map) z v w) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro N he hcompact j hstage I J hJ hJt hIJ hclose
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let B (k : ℕ) (u : ℝ) : RoundCylinderTwoTensor := fun z v w => Q k *
    roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
      (F k ∘ N.coordinate_map) z v w
  let C (u : ℝ) := roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map
  have hsmooth (k : ℕ) (hk : j ≤ k) (u : ℝ) :
      RoundCylinderTensorSmoothOn N.epsilon (B k u) := by
    have htime : t (L.subsequence k) + 0 / Q k ∈ Ico 0 E.flow.base.lifetime :=
      ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ L.limit.base).property
    have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (F k) (L.exhaustion.space k) :=
      (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding k).forward_smooth 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩)
    exact roundCylinderPullback_scaled_smoothOn _ _ N.epsilon (Q k)
      (hF.comp N.coordinate_map_smooth (fun z hz => L.exhaustion.space_increasing hk
        (hstage (subset_closure (N.coordinatePartialDiffeomorph.map_source hz)))))
  have hCsmooth (u : ℝ) : RoundCylinderTensorSmoothOn N.epsilon (C u) := by
    simpa only [one_mul] using roundCylinderPullback_scaled_smoothOn
      (L.limit.flow.metric u) N.coordinate_map N.epsilon 1 N.coordinate_map_smooth
  have hAt (D : RoundCylinderTwoTensor) (hD : RoundCylinderTensorSmoothOn N.epsilon D)
      (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient D (chartAt E2 q) y a b)
        (0, s) := by
    apply (hD q a b).contDiffAt
    apply ((chartAt E2 q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial, hs⟩
  obtain ⟨eta, heta, hmargin⟩ := hclose.exists_same_epsilon_perturbation_margin
    (fun u hu => (hJt (hIJ hu)).trans_lt zero_lt_one)
  obtain ⟨K, hK⟩ := full_cylinder_jet_difference_uniform ⌊N.epsilon⁻¹⌋₊ J hJ
    (fun u hu => (hJt hu).trans_lt zero_lt_one) N.epsilon⁻¹
    (fun k => B (k + j)) (fun _ => C)
    (fun k u _ => hAt _ (hsmooth (k + j) (Nat.le_add_left _ _) u))
    (fun _ u _ => hAt _ (hCsmooth u)) (by
      intro r hr a b d hd
      obtain ⟨K, hK⟩ := blowupSequence_full_neck_coefficient_jets_uniform P E t x ht hR L
        N he hcompact j hstage J hJ hJt r hr a b d hd
      exact ⟨K, fun k hk => hK (k + j) (hk.trans (Nat.le_add_right _ _))⟩) eta heta
  filter_upwards [eventually_ge_atTop (K + j)] with k hk
  have hjk : j ≤ k := by omega
  have hkj : K ≤ k - j := by omega
  apply hmargin (B k) (fun u _ => hsmooth k hjk u)
  intro u hu z hz
  have h := (hK (k - j) hkj u (hIJ hu) z hz).le
  simpa only [Nat.sub_add_cancel hjk] using h

end PoincareConjecture.M35.OrdinaryRealization
