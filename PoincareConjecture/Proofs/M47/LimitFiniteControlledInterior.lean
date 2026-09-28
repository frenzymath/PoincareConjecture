import PoincareConjecture.Proofs.M47.LimitFiniteRetainedInterior
import PoincareConjecture.Proofs.M47.LimitNoncollapseSource
import PoincareConjecture.Proofs.M47.BlowupControlsSequence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

private theorem controlled_zero_image
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale B eta : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (hzero : (0 : ℝ) ∈ I)
    (hbound : ∀ s hs x, x ∈ U →
      |F.curvatureNorm (e.pointMap s hs x)| ≤ B * scale)
    (hnegative : ∀ s hs x, x ∈ U →
      (F.connection (origin + s / scale)).negativeCurvaturePart
        (e.forward s hs x) ≤ eta * scale) :
    ∀ Y : Set (F.slice (origin + 0 / scale)).carrier,
      (∀ y ∈ Y, ∃ x ∈ U,
        e.pointMap 0 hzero x = (⟨origin + 0 / scale, y⟩ : F.point)) →
      ∃ d : GeneralizedFlowCylinder F (F.slice (origin + 0 / scale))
          origin scale I Y,
        (∀ hs y, y ∈ Y →
          d.pointMap 0 hs y = (⟨origin + 0 / scale, y⟩ : F.point)) ∧
        (∀ s hs y, y ∈ Y → |F.curvatureNorm (d.pointMap s hs y)| ≤ B * scale) ∧
        (∀ s hs y, y ∈ Y →
          (F.connection (origin + s / scale)).negativeCurvaturePart
            (d.forward s hs y) ≤ eta * scale) := by
  intro Y capture
  let chart := limitRP2CylinderSliceChart e hU 0 hzero
  have hY : Y ⊆ chart.target := by
    intro y hy
    obtain ⟨x, hx, hpoint⟩ := capture y hy
    exact ⟨x, hx, eq_of_heq (Sigma.mk.inj hpoint).2⟩
  have hmaps : MapsTo chart.symm Y U := fun _ hy => chart.symm.map_source (hY hy)
  let d := limitNoncollapseCylinderSource e chart.symm Y hY hmaps
  refine ⟨d, ?_, ?_, ?_⟩
  · intro hs y hy
    change (⟨origin + 0 / scale, e.forward 0 hs (e.inverse 0 hzero y)⟩ : F.point) = _
    exact congrArg (fun x => (⟨origin + 0 / scale, x⟩ : F.point))
      (e.right_inverse 0 hzero (hY hy))
  · intro s hs y hy
    exact hbound s hs (chart.symm y) (hmaps hy)
  · intro s hs y hy
    exact hnegative s hs (chart.symm y) (hmaps hy)

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (H : ∀ k, M33RegularHistoryData (W k)) (t : ℕ → ℝ)
  (ht : ∀ k, t k ∈ (H k).generalized.interval)
  (x : ∀ k, ((H k).generalized.slice (t k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W H t ht x hPositive hDiverges



theorem limitFinite_controlled_of_preserved_interior
    (k : ℕ) {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier}
    {A T b c B eta : ℝ} (hT : 0 < T) (hb : b < -T) (hU : IsOpen U)
    (E : SurgeryFlowCylinder (F k) C (t k) ((V).scale k) (Icc b 0) U)
    (e0 : GeneralizedFlowCylinder (H k).generalized C (t k) ((V).scale k) (Icc c 0) U)
    (hzero : (0 : ℝ) ∈ Icc c 0)
    (hfuture : ∀ s (hs : s ∈ Icc c 0) (hs' : s ∈ Icc b 0), ∀ z ∈ U,
      E.forward s hs' z = (H k).history.forward (t k + s / (V).scale k)
        (((H k).generalized.slice_nonempty_iff _).mp ⟨e0.forward s hs z⟩)
        (e0.forward s hs z))
    (hbound : ∀ s hs z, z ∈ U →
      |((F k).connection (t k + s / (V).scale k)).curvatureTensorNorm
        (E.forward s hs z)| ≤ B * (V).scale k)
    (hnegative : ∀ s hs z, z ∈ U →
      ((F k).connection (t k + s / (V).scale k)).negativeCurvaturePart
        (E.forward s hs z) ≤ eta * (V).scale k)
    (capture : ∀ y ∈ (V).baseBall k A, ∃ z ∈ U,
      e0.pointMap 0 hzero z = (⟨t k, y⟩ : (H k).generalized.point)) :
    Nonempty (ControlledBlowupCylinder V k A T B eta) := by
  obtain ⟨htime, d, hmap, _hmetric, hagree, _hmetricAgree⟩ :=
    limitFinite_preserved_history_interior (H k) (ht k) hT hb hU E e0 hfuture
  let zero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨neg_nonpos.mpr hT.le, le_rfl⟩
  have hnormD (s : ℝ) (hs : s ∈ Icc (-T) 0) (z : C.carrier) (hz : z ∈ U) :
      |(H k).generalized.curvatureNorm (d.pointMap s hs z)| ≤ B * (V).scale k := by
    change |((H k).generalized.connection (t k + s / (V).scale k)).curvatureTensorNorm
      (d.forward s hs z)| ≤ _
    rw [← (H k).curvature_norm_pullback _ (htime s hs), hmap s hs z hz]
    exact hbound s _ z hz
  have hnegD (s : ℝ) (hs : s ∈ Icc (-T) 0) (z : C.carrier) (hz : z ∈ U) :
      ((H k).generalized.connection (t k + s / (V).scale k)).negativeCurvaturePart
        (d.forward s hs z) ≤ eta * (V).scale k := by
    rw [← (H k).negative_part_pullback _ (htime s hs), hmap s hs z hz]
    exact hnegative s _ z hz
  have hraw := controlled_zero_image d hU zero hnormD hnegD
  rw [show t k + 0 / (V).scale k = t k by simp] at hraw
  obtain ⟨based, hbased, hnorm, hneg⟩ := hraw ((V).baseBall k A) (by
    intro y hy
    obtain ⟨z, hz, hpoint⟩ := capture y hy
    refine ⟨z, hz, ?_⟩
    exact (congrArg
      (fun w => (⟨t k + 0 / (V).scale k, w⟩ : (H k).generalized.point))
      (hagree 0 hzero zero z hz)).trans hpoint)
  exact ⟨{ embedding := based
           zero_identity := hbased
           curvature_bound := hnorm
           negative_curvature_bound := hneg }⟩

end PoincareConjecture.M47
