import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteAnalyticAssembly
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardFlowGluing
import PoincareConjecture.Proofs.M30.Mathlib.InteriorTerminalJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.secondCountable

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in

theorem exists_backward_flow_on_retained_carrier
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    (hFlow : WithinBilinearFlowService.{0})
    {T Tbig tau B : ℝ} {T0 : ℝ≥0∞}
    (htau : 0 < tau) (htauT : tau < T)
    (hT1 : T ≤ 1) (hTT : T < Tbig)
    (hhorizon : ENNReal.ofReal tau < T0)
    {S : PointedFlowSequence 3 (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (Fopen : RicciFlow 3 G.limitCarrier.carrier
      {s : ℝ | s < T / 2 ∧ ENNReal.ofReal (T / 2 - s) < T0})
    (hopenMetric : Fopen.metric = G.limitFlow.flow.metric)
    (hopenJets : ∀ (q : G.limitCarrier.carrier) (m : ℕ)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
      IsCompact K →
      K ⊆ {s : ℝ | s < T / 2 ∧ ENNReal.ofReal (T / 2 - s) < T0} ×ˢ
        (extChartAt (𝓡 3) q).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            ((S.flow (G.subsequence k)).flow.metric z.1).pullbackCoefficients
              ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
                (extChartAt (𝓡 3) q).symm) z.2))
        (iteratedFDeriv ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
            (Fopen.metric z.1).pullbackCoefficients
              (extChartAt (𝓡 3) q).symm z.2)) atTop K)
    (Fbig : ∀ k, RicciFlow 3 (S.carrier k).carrier (Icc (-Tbig) 0))
    (hmetric : ∀ k t, (Fbig k).metric t =
      (S.flow k).flow.metric (t + T / 2))
    (hcurv : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-Tbig) 0,
      ∀ x : (S.carrier k).carrier,
        ((Fbig k).connection t).curvatureTensorNorm x ≤ B)
    (hcompact : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      IsCompact (closure (((Fbig k).metric 0).ball (S.flow k).base R))) :
    let f := fun (q : G.limitCarrier.carrier) (k : ℕ)
        (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      ((Fbig (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 3) q).symm) z.2
    ∃ F : RicciFlow 3 G.limitCarrier.carrier (blowupBackwardInterval T0),
      EqOn F.metric (fun t => Fopen.metric (t + T / 2))
        {t : ℝ | t < 0 ∧ ENNReal.ofReal (-t) < T0} ∧
      ∀ (q : G.limitCarrier.carrier) (m : ℕ)
        (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))),
        IsCompact K →
        K ⊆ blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 3) q).target →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f q k)
            (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 3) q).target))
          (iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
              (F.metric z.1).pullbackCoefficients
                (extChartAt (𝓡 3) q).symm z.2)
            (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 3) q).target)) atTop K := by
  intro f
  let W := {s : ℝ | s < T / 2 ∧ ENNReal.ofReal (T / 2 - s) < T0}
  let V := {t : ℝ | t < 0 ∧ ENNReal.ofReal (-t) < T0}
  let I := {t : ℝ | ENNReal.ofReal (-t) < T0}
  have hVord : V.OrdConnected := by
    refine ⟨?_⟩
    intro x hx y hy z hz
    exact ⟨hz.2.trans_lt hy.1,
      (ENNReal.ofReal_le_ofReal (neg_le_neg hz.1)).trans_lt hx.2⟩
  have htauV : -tau ∈ V :=
    ⟨neg_lt_zero.mpr htau, by simpa only [neg_neg] using hhorizon⟩
  have hhalfV : -tau / 2 ∈ V := by
    refine ⟨by linarith, ?_⟩
    exact (ENNReal.ofReal_le_ofReal (show -(-tau / 2) ≤ tau by linarith)).trans_lt
      hhorizon
  have hVne : V.Nontrivial := ⟨-tau, htauV, -tau / 2, hhalfV, by linarith⟩
  have hshiftTime : (fun t : ℝ => t + T / 2) '' V ⊆ W := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨by linarith [ht.1], ?_⟩
    have heq : T / 2 - (t + T / 2) = -t := by ring
    rw [heq]
    exact ht.2
  let Finterior : RicciFlow 3 G.limitCarrier.carrier V :=
    Fopen.translate (T / 2) hshiftTime hVord hVne
  obtain ⟨Fclosed, hclosedPast, hclosedJets⟩ :=
    exists_finite_terminal_extension_of_big_window_bounds hShi hMixed hFlow
      htau htauT hT1 hTT G hcomplete Fbig hmetric hcurv hcompact
  have hcompat : ∀ t ∈ Ico (-tau) 0, Finterior.metric t = Fclosed.metric t := by
    intro t ht
    change Fopen.metric (t + T / 2) = Fclosed.metric t
    rw [hopenMetric]
    exact (hclosedPast t ht).symm
  obtain ⟨F, hFinterior, hFclosed⟩ :=
    exists_backwardFlow_of_interior_and_closed htau hhorizon Finterior Fclosed hcompat
  refine ⟨F, hFinterior, ?_⟩
  intro q m K hK hKJ
  let c := extChartAt (𝓡 3) q
  let a := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
    ((S.flow (G.subsequence k)).flow.metric z.1).pullbackCoefficients
      ((fun y => ((G.embedding k).toFun (0, y)).2) ∘ c.symm) z.2
  let b := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (Fopen.metric z.1).pullbackCoefficients c.symm z.2
  let gi := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (Finterior.metric z.1).pullbackCoefficients c.symm z.2
  let gc := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (Fclosed.metric z.1).pullbackCoefficients c.symm z.2
  let g := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (F.metric z.1).pullbackCoefficients c.symm z.2
  let d : ℝ × EuclideanSpace ℝ (Fin 3) := (T / 2, 0)
  let shift := fun z : ℝ × EuclideanSpace ℝ (Fin 3) => z + d
  have hshift : Continuous shift := continuous_id.add continuous_const
  have hsource (k : ℕ) : (fun z => a k (z + d)) = f q k := by
    funext z
    change ((S.flow (G.subsequence k)).flow.metric (z.1 + T / 2)).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘ c.symm) (z.2 + 0) =
      ((Fbig (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘ c.symm) z.2
    rw [hmetric, add_zero]
  have htarget : (fun z => b (z + d)) = gi := by
    funext z
    change (Fopen.metric (z.1 + T / 2)).pullbackCoefficients c.symm (z.2 + 0) =
      (Fopen.metric (z.1 + T / 2)).pullbackCoefficients c.symm z.2
    rw [add_zero]
  have hsourceJet (k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin 3)) :
      iteratedFDeriv ℝ m (f q k) z = iteratedFDeriv ℝ m (a k) (shift z) := by
    rw [← hsource k]
    exact iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := a k) m d z
  have htargetJet (z : ℝ × EuclideanSpace ℝ (Fin 3)) :
      iteratedFDeriv ℝ m gi z = iteratedFDeriv ℝ m b (shift z) := by
    rw [← htarget]
    exact iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := b) m d z
  have hinterior : ∀ L : Set (ℝ × EuclideanSpace ℝ (Fin 3)),
      IsCompact L → L ⊆ (I ∩ Iio 0) ×ˢ c.target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f q k)) (iteratedFDeriv ℝ m gi) atTop L := by
    intro L hL hLV
    have himage : shift '' L ⊆ W ×ˢ c.target := by
      rintro _ ⟨z, hz, rfl⟩
      have ht : z.1 ∈ V := ⟨(hLV hz).1.2, (hLV hz).1.1⟩
      have htime := hshiftTime (mem_image_of_mem (fun t : ℝ => t + T / 2) ht)
      change z.1 + T / 2 ∈ W ∧ z.2 + 0 ∈ c.target
      exact ⟨htime, by simpa only [add_zero] using (hLV hz).2⟩
    have H := hopenJets q m (shift '' L) (hL.image hshift) himage
    change TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (a k))
      (iteratedFDeriv ℝ m b) atTop (shift '' L) at H
    have Hcomp := (H.comp shift).mono (show L ⊆ shift ⁻¹' (shift '' L) from
      fun z hz => mem_image_of_mem shift hz)
    apply (Hcomp.congr ?_).congr_right ?_
    · exact Eventually.of_forall fun k z _ => (hsourceJet k z).symm
    · exact fun z _ => (htargetJet z).symm
  have hI : IsOpen I :=
    isOpen_Iio.preimage (ENNReal.continuous_ofReal.comp continuous_neg)
  have hJ : blowupBackwardInterval T0 = I ∩ Iic 0 := by
    ext t
    exact and_comm
  have hiEq : EqOn g gi ((I ∩ Iio 0) ×ˢ c.target) := by
    intro z hz
    change (F.metric z.1).pullbackCoefficients c.symm z.2 =
      (Finterior.metric z.1).pullbackCoefficients c.symm z.2
    rw [hFinterior ⟨hz.1.2, hz.1.1⟩]
  have hcEq : EqOn g gc (Icc (-tau) 0 ×ˢ c.target) := by
    intro z hz
    change (F.metric z.1).pullbackCoefficients c.symm z.2 =
      (Fclosed.metric z.1).pullbackCoefficients c.symm z.2
    rw [hFclosed hz.1]
  change TendstoUniformlyOn
    (fun k => iteratedFDerivWithin ℝ m (f q k) (blowupBackwardInterval T0 ×ˢ c.target))
    (iteratedFDerivWithin ℝ m g (blowupBackwardInterval T0 ×ˢ c.target)) atTop K
  rw [hJ] at hKJ ⊢
  exact tendstoUniformlyOn_iteratedFDerivWithin_of_interior_and_terminal hI
    (isOpen_extChartAt_target (I := 𝓡 3) q) htau hiEq hcEq m hinterior
    (fun L hL hLC => hclosedJets q m L hL hLC) hK hKJ

end PoincareConjecture.M30
