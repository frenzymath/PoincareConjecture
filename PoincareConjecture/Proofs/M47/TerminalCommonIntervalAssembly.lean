import PoincareConjecture.Proofs.M47.TerminalCommonIntervalInterior
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSearch
import PoincareConjecture.Proofs.M04.ShiCarrier









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (H : ∀ k, M33RegularHistoryData (W k)) (t : ℕ → ℝ)
  (ht : ∀ k, t k ∈ (H k).generalized.interval)
  (x : ∀ k, ((H k).generalized.slice (t k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (t k)).scalarCurvature
    ((H k).history.forward (t k) (ht k) (x k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W H t ht x hPositive hDiverges



theorem terminalCommonInterval_physical_scalar
    (k : ℕ) {A K : ℝ}
    (himage : ((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
      (A / Real.sqrt ((V).scale k)) ⊆ range ((H k).history.forward (t k) (ht k)))
    (hscalar : ∀ y ∈ (V).baseBall k A,
      ((V).flow k).scalar ⟨((V).base k).1, y⟩ ≤ (2 * K) * (V).scale k) :
    ∀ y ∈ ((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
        (A / Real.sqrt ((V).scale k)),
      ((F k).connection (t k)).scalarCurvature y ≤ (2 * K) * (V).scale k := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := ((H k).history.ball_image_of_subset (t k) (ht k) (x k)
    (A / Real.sqrt ((V).scale k)) himage).symm ▸ hy
  rw [(H k).scalar_pullback]
  exact hscalar z hz



theorem terminalCommonInterval_controlled_of_long_search
    (k : ℕ) {A a tau B eta : ℝ} (hA : 0 < A) (htau : 0 < tau) (ha : a < -tau)
    (e : SurgeryFlowCylinder (F k) ((F k).slice (t k)) (t k) ((V).scale k) (Icc a 0)
      (((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
        (A / Real.sqrt ((V).scale k))))
    (hbased : ∀ hs y, y ∈ ((F k).metric (t k)).ball
      ((H k).history.forward (t k) (ht k) (x k)) (A / Real.sqrt ((V).scale k)) →
        HEq (e.forward 0 hs y) y)
    (hcurv : ∀ s (hs : s ∈ Icc a 0), ∀ y ∈ ((F k).metric (t k)).ball
        ((H k).history.forward (t k) (ht k) (x k)) (A / Real.sqrt ((V).scale k)),
      |((F k).connection (t k + s / (V).scale k)).curvatureTensorNorm (e.forward s hs y)| ≤
        B * (V).scale k)
    (hneg : ∀ s (hs : s ∈ Icc a 0), ∀ y ∈ ((F k).metric (t k)).ball
        ((H k).history.forward (t k) (ht k) (x k)) (A / Real.sqrt ((V).scale k)),
      ((F k).connection (t k + s / (V).scale k)).negativeCurvaturePart (e.forward s hs y) ≤
        eta * (V).scale k) :
    Nonempty (ControlledBlowupCylinder V k A tau B eta) := by
  let U : TopologicalSpace.Opens ((F k).slice (t k)).carrier :=
    ⟨((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
      (A / Real.sqrt ((V).scale k)), M04.initial_ball_isOpen _ _ _⟩
  have hx : (H k).history.forward (t k) (ht k) (x k) ∈ U := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : ((F k).slice (t k)).carrier → Type _) :=
      ⟨((F k).metric (t k)).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3)
      ((H k).history.forward (t k) (ht k) (x k))
      ((H k).history.forward (t k) (ht k) (x k)) <
        ENNReal.ofReal (A / Real.sqrt ((V).scale k))
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hA (Real.sqrt_pos.mpr ((V).base_scalar_pos k)))
  obtain ⟨_htime, d, hzero, _hmap, _hmetric, hbound⟩ := terminalCommonInterval_history_interior
    (H k) (ht k) htau ha U ⟨_, hx⟩ e hbased hcurv hneg
  have hpre : (H k).history.forward (t k) (ht k) ⁻¹' U = (V).baseBall k A :=
    terminalCommonInterval_ball_preimage (H k) (ht k) (by linarith only [ha, htau])
      (x k) e hbased
  have hraw : ∃ d : GeneralizedFlowCylinder ((V).flow k) (((V).flow k).slice ((V).base k).1)
      ((V).base k).1 ((V).scale k) (Icc (-tau) 0)
        ((H k).history.forward (t k) (ht k) ⁻¹' U),
      (∀ hs y, y ∈ (H k).history.forward (t k) (ht k) ⁻¹' U →
        d.pointMap 0 hs y = (⟨((V).base k).1, y⟩ : ((V).flow k).point)) ∧
      (∀ s hs y, y ∈ (H k).history.forward (t k) (ht k) ⁻¹' U →
        |((V).flow k).curvatureNorm (d.pointMap s hs y)| ≤ B * (V).scale k ∧
        (((V).flow k).connection (((V).base k).1 + s / (V).scale k)).negativeCurvaturePart
          (d.forward s hs y) ≤ eta * (V).scale k) := ⟨d, hzero, hbound⟩
  rw [hpre] at hraw
  obtain ⟨d, hd0, hdb⟩ := hraw
  exact ⟨{ embedding := d
           zero_identity := hd0
           curvature_bound := fun s hs y hy => (hdb s hs y hy).1
           negative_curvature_bound := fun s hs y hy => (hdb s hs y hy).2 }⟩



theorem terminalCommonInterval_controlled_or_cap
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    {K : ℝ} (hK : 1 ≤ K) (P : M46Predecessors.{u})
    (k : ℕ) (p : SurgeryParameterPrefix S.constants) (O : SurgeryObservation (F k))
    (hInitial : (F k).standard_initial = S.setup.standard_initial)
    (hConstants : (F k).local_constants = S.constants) (hC : (F k).parameters.C = S.setup.C)
    {r A eta : ℝ} (hA : 0 < A) (heta : 0 < eta)
    (hBase : t k ∈ Ico (surgeryEpochStart p.i) O.H)
    (hScale : 64 * (2 * terminalCommonIntervalDuration S B K + 1) ≤ (V).scale k)
    (hLarge : B.curvature_threshold ≤ (V).scale k) (hThreshold : r⁻¹ ^ 2 ≤ (V).scale k)
    (hPinched : SurgeryFlowPinched (F k))
    (hEarlier : SurgeryCanonicalOn (F k) (surgeryObservationInterval O ∩ Iio (t k)) r)
    (hOverlap : ∀ s ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      (F k).parameters.delta s ≤ B.delta S.setup.standard_initial S.constants)
    (hTerminal : ∀ y ∈ ((F k).metric (t k)).ball
        ((H k).history.forward (t k) (ht k) (x k)) (A / Real.sqrt ((V).scale k)),
      ((F k).connection (t k)).scalarCurvature y ≤ (2 * K) * (V).scale k)
    (hPinchingScale : blowupPinchingThreshold (8 * K) eta ≤ (V).scale k) :
    Nonempty (ControlledBlowupCylinder V k A (terminalCommonIntervalDuration S B K)
      (13 * max (8 * K) 1) eta) ∨
    ∃ (a : ℝ) (ha : a ∈ Icc (-terminalCommonIntervalDuration S B K) 0),
      ∃ e : SurgeryFlowCylinder (F k) ((F k).slice (t k)) (t k) ((V).scale k) (Icc a 0)
        (((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
          (A / Real.sqrt ((V).scale k))),
        (∀ hs y, y ∈ ((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
          (A / Real.sqrt ((V).scale k)) → HEq (e.forward 0 hs y) y) ∧
        (∀ s (hs : s ∈ Icc a 0), ∀ y ∈ ((F k).metric (t k)).ball
            ((H k).history.forward (t k) (ht k) (x k)) (A / Real.sqrt ((V).scale k)),
          ((F k).connection (t k + s / (V).scale k)).scalarCurvature (e.forward s hs y) ≤
            (8 * K) * (V).scale k) ∧
        ∃ hT : t k + a / (V).scale k ∈ (F k).surgery_times,
          ∀ [Nonempty ((F k).slice (t k + a / (V).scale k)).carrier],
            ∃ i : Fin ((F k).event (t k + a / (V).scale k) hT).cap_count,
              (e.forward a ⟨le_rfl, ha.2⟩ ''
                  (((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
                    (A / Real.sqrt ((V).scale k))) ∩
                (((F k).event (t k + a / (V).scale k) hT).caps i).carrier).Nonempty := by
  let U := ((F k).metric (t k)).ball ((H k).history.forward (t k) (ht k) (x k))
    (A / Real.sqrt ((V).scale k))
  have hx : (H k).history.forward (t k) (ht k) (x k) ∈ U := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : ((F k).slice (t k)).carrier → Type _) :=
      ⟨((F k).metric (t k)).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3)
      ((H k).history.forward (t k) (ht k) (x k))
      ((H k).history.forward (t k) (ht k) (x k)) <
        ENNReal.ofReal (A / Real.sqrt ((V).scale k))
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hA (Real.sqrt_pos.mpr ((V).base_scalar_pos k)))
  obtain ⟨a, _ha, e, hbased, hbounds, hstop⟩ :=
    terminalCommonInterval_exists_bounded_search S B hK p O hInitial hConstants hC
      hBase hScale hLarge hThreshold hPinched hEarlier hOverlap P U
      (M04.initial_ball_isOpen _ _ _) ⟨_, hx⟩ hTerminal heta hPinchingScale
  rcases hstop with hlong | ⟨hshort, hcap⟩
  · exact Or.inl (terminalCommonInterval_controlled_of_long_search F W H t ht x
      hPositive hDiverges k hA (terminalCommonInterval_duration_bounds S B hK).1
      hlong e hbased (fun s hs y hy => (hbounds s hs y hy).2.1)
      (fun s hs y hy => (hbounds s hs y hy).2.2))
  · exact Or.inr ⟨a, hshort, e, hbased, fun s hs y hy => (hbounds s hs y hy).1, hcap⟩

end PoincareConjecture.M47
