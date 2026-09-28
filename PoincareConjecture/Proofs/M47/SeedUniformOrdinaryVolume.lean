import PoincareConjecture.Proofs.M47.SeedOrdinaryGeometry
import PoincareConjecture.Proofs.M47.SeedThreeStopScales
import PoincareConjecture.Proofs.M47.SeedMidpointVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_uniform_ordinary_birth_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {H R : ℝ} (hH : 0 < H)
    (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) (hR : 0 < R) :
    ∃ V : ℝ, 0 < V ∧ ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryPrefixControls p F O → SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      ∀ (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ) (I : Set ℝ)
        (U : TopologicalSpace.Opens C.carrier)
        (_hcompact : IsCompact (U : Set C.carrier)),
        IsConnected (U : Set C.carrier) →
        ∀ (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I),
          origin + s / scale ∈ surgeryObservationInterval O ∩ prefixFinalInterval p →
          ∀ (g : RiemannianMetric 3 U) (D : LeviCivitaData g),
            (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
              g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
                (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
                (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w)) →
            (∀ y : U, D.scalarCurvature y =
              (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs y.val)) →
            (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
              0 ≤ D.curvatureTensor y v w v w) →
            ∀ q : U, (∀ y ∈ g.ball q R, D.scalarCurvature y ≤ 2 * H) →
              (origin + s / scale = 0 ∨
                ¬ SurgeryPositiveComponentAt F (origin + s / scale) (e.forward s hs q.val) ∨
                ∃ hT : origin + s / scale ∈ F.surgery_times,
                  ∀ [Nonempty (F.slice (origin + s / scale)).carrier],
                    ∃ i : Fin (F.event (origin + s / scale) hT).cap_count,
                      (connectedComponent (e.forward s hs q.val) ∩
                        ((F.event (origin + s / scale) hT).caps i).carrier).Nonempty) →
              ENNReal.ofReal V ≤ calibratedMetricVolume g (g.ball q (R / 2)) := by
  obtain ⟨V0, hV0, hvolume⟩ := exists_uniform_birth_ball_volume P S p compatible hH hlevel
    (show 0 < R / 4 by positivity)
  let r0 := min (R / 8) 1
  let V := min V0 ((euclideanUnitBallLebesgueVolume.toReal / 2) * r0 ^ 3)
  have hr0 : 0 < r0 := by dsimp only [r0]; positivity
  have hV : 0 < V := lt_min hV0 (mul_pos initial_seed_density_pos (pow_pos hr0 3))
  refine ⟨V / 8, by positivity, ?_⟩
  intro F O old hpinch hpolicy C origin scale I U hcompact hconnected e s hs htime
    g D hmetric hread hsec q hscalar hbirth
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  have hphysical : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (origin + s / scale))
      ((F.metric (origin + s / scale)).ball (e.forward s hs q.val) (R / 8)) := by
    rcases hbirth with hzero | hbirth
    · have initial (t : ℝ) (ht : t = 0) (x : (F.slice t).carrier) :
          ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric t)
            ((F.metric t).ball x (R / 8)) := by
        subst t
        apply (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
        apply (seed_initial_ball_volume F x hr0 (min_le_right _ _)).trans (measure_mono ?_)
        intro y hy
        exact hy.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      exact initial _ hzero _
    · have hbound := seed_ordinary_scalar_ball_bound U e s hs g D hmetric hread q hR hscalar
      have hRic := seed_ordinary_component_ricci_nonnegative U hcompact hconnected
        e s hs g D hmetric hsec q
      have hv := hvolume F O old hpinch hpolicy _ htime (e.forward s hs q.val)
        (by simpa only [show 2 * (R / 4) = R / 2 by ring] using hbound) hRic hbirth
      apply (ENNReal.ofReal_le_ofReal (show V ≤ V0 from min_le_left _ _)).trans
      simpa only [div_div, show (4 : ℝ) * 2 = 8 by norm_num] using hv
  apply seed_ordinary_birth_volume U e s hs g hmetric q (by positivity : 0 < R / 2)
  apply hphysical.trans (measure_mono ?_)
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : R / 8 ≤ (R / 2) / 2))

theorem seed_midpoint_volume_of_birth_floor
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {J : Set ℝ} (G : RicciFlow 3 M J)
    {b v A L R V : ℝ} (q : M) (hR : 0 < R) (hA : 1 ≤ A) (hL : 0 < L)
    (hv : 0 ≤ v) (hJ : Icc b (b + v) ⊆ J)
    (hsec : ∀ s ∈ Icc b (b + v), ∀ x : M, ∀ w z : TangentSpace (𝓡 3) x,
      0 ≤ (G.connection s).curvatureTensor x w z w z)
    (hscalar : ∀ x ∈ closure ((G.metric b).ball q R), ∀ s ∈ Icc b (b + v),
      (G.connection s).scalarCurvature x ≤ 8 * L)
    (hbudget : A * L * v ≤ 1 / 64)
    (hvolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.metric b) ((G.metric b).ball q (R / 2))) :
    ENNReal.ofReal (V / 8) ≤ calibratedMetricVolume (G.metric (b + v / 2))
      ((G.metric (b + v / 2)).ball q (R / 2)) := by
  have hpow : (R / 2) ^ 3 ≠ 0 := ne_of_gt (pow_pos (by positivity : 0 < R / 2) 3)
  have h := seed_midpoint_volume G q hR hA hL hv hJ hsec hscalar hbudget
    (k := V / (R / 2) ^ 3) (by simpa only [div_mul_cancel₀ _ hpow] using hvolume)
  convert h using 1
  field_simp

end PoincareConjecture.Proofs.M47
