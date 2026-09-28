import PoincareConjecture.Proofs.M47.SeedYoungAccessibleVolume
import PoincareConjecture.Proofs.M47.SeedNormalizedPhysical










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_seed_young_physical_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ A kappa : ℝ, 1 ≤ A ∧ 0 < kappa ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          M46.ObservedInputs p rNext cutoff F O →
        ∀ T a : ℝ, a < 0 → -a ≤ rNext ^ 2 / (32 * A) →
          T ∈ Ico (surgeryEpochStart p.i) O.H →
          Icc (T + a) T ⊆ surgeryObservationInterval O →
        ∀ U : TopologicalSpace.Opens (F.slice T).carrier,
          IsCompact (U : Set (F.slice T).carrier) →
          IsConnected (U : Set (F.slice T).carrier) →
        ∀ (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U),
          (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
        ∀ G : RicciFlow 3 U (Icc (T + a) T),
          (∀ s (hs : s ∈ Icc a 0) (y : U) (v w : TangentSpace (𝓡 3) y),
            (F.metric (T + s / 1)).inner (e.forward s hs y.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) =
                (G.metric (T + s / 1)).inner y v w) →
          (∀ s (hs : s ∈ Icc a 0) (y : U),
            (G.connection (T + s / 1)).scalarCurvature y =
              (F.connection (T + s / 1)).scalarCurvature (e.forward s hs y.val)) →
          (∀ s (hs : s ∈ Icc a 0) (y : U),
            (G.connection (T + s / 1)).curvatureTensorNorm y =
              (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs y.val)) →
          (∀ t ∈ Icc (T + a) T, ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
            0 ≤ (G.connection t).curvatureTensor y v w v w) →
          ∀ hs : a ∈ Icc a 0,
            (∀ q : U,
              ¬ SurgeryPositiveComponentAt F (T + a / 1) (e.forward a hs q.val) ∨
                ∃ hT : T + a / 1 ∈ F.surgery_times,
                  ∀ [Nonempty (F.slice (T + a / 1)).carrier],
                    ∃ i : Fin (F.event (T + a / 1) hT).cap_count,
                      (connectedComponent (e.forward a hs q.val) ∩
                        ((F.event (T + a / 1) hT).caps i).carrier).Nonempty) →
          ∀ (x : U) (r : ℝ), 0 < r → r ^ 2 ≤ 8 * (-a) →
          ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
            ((F.metric T).ball x.val r),
            (∀ hs y, y ∈ (F.metric T).ball x.val r → HEq (test.forward 0 hs y) y) →
            (∀ s (hs : s ∈ Icc (-r ^ 2) 0), ∀ y ∈ (F.metric T).ball x.val r,
              (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤ r⁻¹ ^ 2) →
            ENNReal.ofReal (kappa * r ^ 3) ≤
              calibratedMetricVolume (F.metric T) ((F.metric T).ball x.val r) := by
  obtain ⟨A, V, hA, hV, accessible⟩ := exists_seed_young_accessible_volume P S N p hp
  obtain ⟨Q⟩ := P.m15.uniform 1 2 V (by norm_num) (by norm_num) hV
  refine ⟨A, Q.kappa / 64, hA, div_pos Q.kappa_pos (by norm_num), ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, seeds⟩ := accessible rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O inputs T a ha hyoung hT hobs U hcompact hconnected e he G
    hmetric hscalar hnorm hsec hsBirth hbirth x r hr hsize test hbased hcurv
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  have hclock : T + a - T = a := by ring
  have hage : T - (T + a) = -a := by ring
  have hsub : Icc (T + a - T) 0 ⊆ Icc a 0 := by rw [hclock]
  let e' := e.restrict hsub ordConnected_Icc (Subset.refl (U : Set (F.slice T).carrier))
  have hbirthAt (s : ℝ) (hs : s ∈ Icc a 0) (hsa : s = a) : ∀ q : U,
      ¬ SurgeryPositiveComponentAt F (T + s / 1) (e.forward s hs q.val) ∨
      ∃ hT : T + s / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (T + s / 1)).carrier],
          ∃ i : Fin (F.event (T + s / 1) hT).cap_count,
            (connectedComponent (e.forward s hs q.val) ∩
                ((F.event (T + s / 1) hT).caps i).carrier).Nonempty := by
    subst s
    exact hbirth
  obtain ⟨tau, hlo, htau, E, hE, haccess, hvolume⟩ :=
    seeds F O inputs (T + a) T (by linarith) (by rwa [hage]) hT hobs U hcompact hconnected
      e' G (fun s hs => hmetric s (hsub hs)) (fun s hs => hscalar s (hsub hs)) hsec
      (by rw [hclock]; exact hsBirth)
      (hbirthAt (T + a - T) (by rwa [hclock]) hclock) x
  exact seedM15_normalized_physical_volume P.m12 P.m13 P.m14 P.ordinary Q
    ha U e he G hmetric hnorm x (by rwa [hage] at htau) (by rwa [hage] at hlo)
    E hE haccess (by rwa [hage] at hvolume) hr hsize test hbased hcurv

end PoincareConjecture.Proofs.M47
