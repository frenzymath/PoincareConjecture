import PoincareConjecture.Proofs.M35.Thm12_28.UniformNeckJets
import PoincareConjecture.Proofs.M35.Thm12_28.NeckPullbackSmoothness
import PoincareConjecture.Proofs.M35.Thm12_28.NeckJetTransfer

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_neck_family_close (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : RoundCylinderSpace → L.limit.sliceCarrier.carrier)
      (delta epsilon : ℝ) (_hd : 0 < delta) (_he : 0 < epsilon)
      (_hde : delta ≤ epsilon / 4)
      (_hcoord : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
        (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹))
      (j : ℕ) (_hspace : MapsTo coordinate (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹)
        (L.exhaustion.space j))
      (I J : Set ℝ) (_hJ : IsCompact J) (_hJt : J ⊆ Iic 0) (_hIJ : I ⊆ J)
      (_hC : RoundCylinderFamilyClose delta I
        (fun u => roundCylinderPullback (L.limit.flow.metric u) coordinate)),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      ∃ N : ℕ, ∀ k ≥ N, RoundCylinderFamilyClose epsilon I
        (fun u z v w => Q k *
          roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
            (F k ∘ coordinate) z v w) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate delta epsilon hd he hde hcoord j hspace I J hJ hJt hIJ hC
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let B (k : ℕ) (u : ℝ) : RoundCylinderTwoTensor := fun z v w => Q k *
    roundCylinderPullback (E.flow.metric (t (L.subsequence k) + u / Q k))
      (F k ∘ coordinate) z v w
  have hinv : epsilon⁻¹ < delta⁻¹ := inv_strictAnti₀ hd (by linarith)
  have hinside : (univ : Set UnitTwoSphere) ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹ ⊆
      univ ×ˢ Ioo (-delta⁻¹) delta⁻¹ := by
    intro z hz
    exact ⟨mem_univ _, (neg_lt_neg hinv).trans_le hz.2.1, hz.2.2.trans_lt hinv⟩
  have hsmooth (k : ℕ) (hk : j ≤ k) (u : ℝ) :
      RoundCylinderTensorSmoothOn delta (B k u) := by
    have htime : t (L.subsequence k) + 0 / Q k ∈ Ico 0 E.flow.base.lifetime :=
      ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ L.limit.base).property
    have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (F k) (L.exhaustion.space k) :=
      (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding k).forward_smooth 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩)
    exact roundCylinderPullback_scaled_smoothOn _ _ delta (Q k)
      (hF.comp hcoord (fun z hz => L.exhaustion.space_increasing hk (hspace hz)))
  have hsmoothAt (D : RoundCylinderTwoTensor) (hD : RoundCylinderTensorSmoothOn delta D)
      (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Icc (-epsilon⁻¹) epsilon⁻¹) (a b : Fin 3) :
      ContDiffAt ℝ ∞ (fun y => roundCylinderTensorCoefficient D
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) y a b) (0, s) := by
    apply (hD q a b).contDiffAt
    apply ((chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [sphere_chart_target]; trivial,
      (neg_lt_neg hinv).trans_le hs.1, hs.2.trans_lt hinv⟩
  have hCsmooth (u : ℝ) : RoundCylinderTensorSmoothOn delta
      (roundCylinderPullback (L.limit.flow.metric u) coordinate) := by
    simpa only [one_mul] using
      roundCylinderPullback_scaled_smoothOn (L.limit.flow.metric u) coordinate delta 1 hcoord
  obtain ⟨N, hN⟩ := cylinder_jet_difference_uniform ⌊epsilon⁻¹⌋₊ J hJ
    (fun u hu => (hJt hu).trans_lt zero_lt_one) epsilon⁻¹
    (fun k => B (k + j))
    (fun _ u => roundCylinderPullback (L.limit.flow.metric u) coordinate)
    (fun k u _ => hsmoothAt _ (hsmooth (k + j) (Nat.le_add_left _ _) u))
    (fun _ u _ => hsmoothAt _ (hCsmooth u)) (by
      intro r _ a b eta heta
      obtain ⟨K, hK⟩ := blowupSequence_neck_coefficient_jets_uniform P E t x ht hR L
        coordinate (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) (isOpen_univ.prod isOpen_Ioo)
        hcoord epsilon⁻¹ hinside j (fun q s hs => hspace (hinside ⟨mem_univ q, hs⟩))
        J hJ hJt r a b eta heta
      exact ⟨K, fun k hk => hK (k + j) (hk.trans (Nat.le_add_right _ _))⟩)
    (epsilon ^ 2 / 8) (by positivity)
  refine ⟨N + j, fun k hk => ?_⟩
  have hjk : j ≤ k := by omega
  have hkj : N ≤ k - j := by omega
  apply hC.perturb_of_jet_difference_le (eta := epsilon ^ 2 / 8) hd (by linarith)
    (fun u hu => (hJt (hIJ hu)).trans_lt zero_lt_one)
  · intro u _ q a b
    exact (hsmooth k hjk u q a b).mono
      (prod_mono subset_rfl (Ioo_subset_Ioo (neg_le_neg hinv.le) hinv.le))
  · have hsq := pow_le_pow_left₀ hd.le hde 2
    nlinarith [sq_pos_of_pos he]
  · intro u hu z hz
    have h := (hN (k - j) hkj u (hIJ hu) z ⟨hz.1.le, hz.2.le⟩).le
    simpa only [Nat.sub_add_cancel hjk] using h

end PoincareConjecture.M35.OrdinaryRealization
