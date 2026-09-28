import PoincareConjecture.Proofs.M47.SeedYoungJointBuffer
import PoincareConjecture.Proofs.M47.SeedYoungBirthVolume
import PoincareConjecture.Proofs.M47.SeedYoungMidpointVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_young_accessible_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ A V : ℝ, 1 ≤ A ∧ 0 < V ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          M46.ObservedInputs p rNext cutoff F O →
        ∀ b T : ℝ, b < T → T - b ≤ rNext ^ 2 / (32 * A) →
          T ∈ Ico (surgeryEpochStart p.i) O.H →
          Icc b T ⊆ surgeryObservationInterval O →
        ∀ U : TopologicalSpace.Opens (F.slice T).carrier,
          IsCompact (U : Set (F.slice T).carrier) →
          IsConnected (U : Set (F.slice T).carrier) →
        ∀ (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (b - T) 0) U)
          (G : RicciFlow 3 U (Icc b T)),
          (∀ s (hs : s ∈ Icc (b - T) 0) (y : U) (v w : TangentSpace (𝓡 3) y),
            (F.metric (T + s / 1)).inner (e.forward s hs y.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                (G.metric (T + s / 1)).inner y v w) →
          (∀ s (hs : s ∈ Icc (b - T) 0) (y : U),
            (G.connection (T + s / 1)).scalarCurvature y =
              (F.connection (T + s / 1)).scalarCurvature (e.forward s hs y.val)) →
          (∀ t ∈ Icc b T, ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
            0 ≤ (G.connection t).curvatureTensor y v w v w) →
          ∀ hs : b - T ∈ Icc (b - T) 0,
            (∀ q : U,
              ¬ SurgeryPositiveComponentAt F (T + (b - T) / 1) (e.forward (b - T) hs q.val) ∨
                ∃ hT : T + (b - T) / 1 ∈ F.surgery_times,
                  ∀ [Nonempty (F.slice (T + (b - T) / 1)).carrier],
                    ∃ i : Fin (F.event (T + (b - T) / 1) hT).cap_count,
                      (connectedComponent (e.forward (b - T) hs q.val) ∩
                        ((F.event (T + (b - T) / 1) hT).caps i).carrier).Nonempty) →
          ∀ x : U, ∃ tau : ℝ, 3 * (T - b) / 4 ≤ tau ∧ tau < T - b ∧
            ∃ E : Set U, IsOpen E ∧
              (∀ y ∈ E, reducedLength G T x y tau ≤ 2) ∧
              ENNReal.ofReal (V * Real.sqrt (T - b) ^ 3) ≤
                calibratedMetricVolume (G.metric (T - tau)) E := by
  obtain ⟨A, alpha, B, hA, halpha, _halphaHalf, hB, joint⟩ :=
    exists_seed_young_joint_buffer P S p hp
  obtain ⟨Vbirth, hVbirth, birth⟩ :=
    exists_seed_young_ordinary_birth_volume P S N p hp hA halpha hB
  let V := Real.exp (-6 * B) * Vbirth
  refine ⟨A, V, hA, mul_pos (Real.exp_pos _) hVbirth, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, birthVolume⟩ := birth rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O inputs b T hbT hyoung hT hobs U hcompact hconnected e G metric scalar hsec
    hsBirth hbirth x
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  obtain ⟨v, q, hv, hbirthScalar, hearlyScalar, access, hage, hageTop⟩ :=
    joint rNext cutoff hrNext F O inputs b T hbT hyoung hobs U hcompact hconnected
      e G metric scalar hsec x
  have hd : 0 < T - b := sub_pos.mpr hbT
  have hvpos : 0 < v := (mul_pos halpha hd).trans_le hv.1
  have hApos : 0 < A := zero_lt_one.trans_le hA
  let R := Real.sqrt (alpha * (T - b)) / (4 * A)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hclock : T + (b - T) / 1 = b := by simp
  have hmetric (y : U) (v w : TangentSpace (𝓡 3) y) :
      (G.metric b).inner y v w =
        (F.metric (T + (b - T) / 1)).inner (e.forward (b - T) hsBirth y.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward (b - T) hsBirth z.val) y v)
          (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward (b - T) hsBirth z.val) y w) :=
    ((metric (b - T) hsBirth y v w).trans
      (congrArg (fun t => (G.metric t).inner y v w) hclock)).symm
  have hscalar (y : U) : (G.connection b).scalarCurvature y =
      (F.connection (T + (b - T) / 1)).scalarCurvature
        (e.forward (b - T) hsBirth y.val) :=
    (congrArg (fun t => (G.connection t).scalarCurvature y) hclock).symm.trans
      (scalar (b - T) hsBirth y)
  have hfuture : T + (b - T) / 1 + (T - b) ∈ Ico (surgeryEpochStart p.i) O.H := by
    simpa only [hclock, add_sub_cancel] using hT
  have hbVolume := birthVolume F O inputs (F.slice T) T 1 (Icc (b - T) 0)
    U hcompact e (b - T) hsBirth (T - b) hd hyoung hfuture
    (G.metric b) (G.connection b) hmetric hscalar q
    (fun y hy => hbirthScalar y (subset_closure hy)) (hbirth q)
  have hJ : Icc b (b + v) ⊆ Icc b T := by
    apply Icc_subset_Icc le_rfl
    linarith only [hv.2, hbT]
  have hmid := seed_young_midpoint_volume G q hd (zero_le_one.trans hB) hR
    hvpos.le hv.2 hJ (fun t ht => hsec t (hJ ht)) hearlyScalar hbVolume
  let E := (G.metric (b + v / 2)).ball q (R / 2)
  have hE : IsOpen E := isOpen_Iio.preimage
    ((M36.metric_edist_continuous (G.metric (b + v / 2))).comp
      (continuous_const.prodMk continuous_id))
  refine ⟨T - b - v / 2, hage, hageTop, E, hE, access, ?_⟩
  have hmidClock : T - (T - b - v / 2) = b + v / 2 := by ring
  simpa only [hmidClock, V, mul_assoc] using hmid

end PoincareConjecture.Proofs.M47
