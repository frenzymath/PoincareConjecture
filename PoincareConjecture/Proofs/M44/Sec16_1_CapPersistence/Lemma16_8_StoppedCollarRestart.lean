import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedCollar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance restartCollarCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restartCollarCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance restartCollarTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance restartCollarTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem exists_stopped_local_collar_restart (P : M44CapPersistencePredecessors.{u})
    (C : ℝ) (u v : E) {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C u v)
    {K H r alpha beta Z : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hZ : 1 ≤ Z) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ {a T : ℝ}, 0 ≤ a → a < T → T ≤ H → T - a ≤ tau →
      ∀ F : RicciFlow 3 M (Icc 0 T),
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞,
      (∀ j ≤ 2, ∀ y ∈ e.target, (F.connection 0).curvatureDerivativeNorm j y ≤ K) →
      ∀ {V : Set E}, IsOpen V → V ⊆ e.source →
      (∀ y ∈ V, IsCompact (closure ((F.metric 0).ball (e y) r))) →
      (∀ y ∈ V, closure ((F.metric 0).ball (e y) r) ⊆ e.target) →
      (∀ y ∈ V, ∀ w, alpha * ‖w‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e y w w) →
      (∀ y ∈ V, ∀ w, (F.metric 0).pullbackCoefficients e y w w ≤ beta * ‖w‖ ^ 2) →
      (∀ y ∈ V, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) y‖ ≤ Z) →
      ∀ x ∈ V, ∀ J ∈ model,
      ‖metricTwoJet ((F.metric a).pullbackCoefficients e) x - J‖ ≤ delta →
      (∀ c ∈ Ioc a T,
        (∀ s ∈ Ico a c, ∃ p q : TangentSpace (𝓡 3) (e x),
          LeviCivitaData.IsOrthonormalPair (F.metric s) (e x) p q ∧
          (F.connection s).sectionalCurvature (e x) p q <
            C⁻¹ * (F.connection s).scalarCurvature (e x)) →
        ∀ s ∈ Icc (0 : ℝ) c, ∀ y ∈ e.target, (F.connection s).curvatureTensorNorm y ≤ K) →
      (∀ t ∈ Icc a T,
        metricTwoJet ((F.metric t).pullbackCoefficients e) x ∈ collarJetRegion C u v) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ e.target, (F.connection t).curvatureTensorNorm y ≤ K) := by
  obtain ⟨_, L, _, hL, hmod⟩ := exists_local_coordinate_modulus P 2 hK hH hr halpha hbeta hZ
  obtain ⟨d, tau, hd, htau, hpreserve⟩ :=
    exists_collar_jet_time_margin C u v hmodel hmargin hL
  obtain ⟨d0, hd0, hinitialMargin⟩ := exists_uniform_collar_jet_margin C u v hmodel hmargin
  refine ⟨min d d0, tau, lt_min hd hd0, htau, ?_⟩
  intro M _ _ _ _ _ a T ha haT hTH hTtau F e hinitial V hV hsub hcompact hinside
    hlower hupper hjets x hx J hJ hnear hcontrolled
  let f : ℝ → MetricTwoJet 3 := fun t => metricTwoJet ((F.metric t).pullbackCoefficients e) x
  have hinv : ∀ y ∈ e.source, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible := by
    intro y hy
    exact ⟨(e.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  have hplane (s : ℝ) (hs : f s ∈ collarJetRegion C u v) :
      ∃ p q : TangentSpace (𝓡 3) (e x),
        LeviCivitaData.IsOrthonormalPair (F.metric s) (e x) p q ∧
        (F.connection s).sectionalCurvature (e x) p q <
          C⁻¹ * (F.connection s).scalarCurvature (e x) :=
    exists_collar_plane_of_pullback_twoJet (F.metric s) (F.connection s)
      e.open_source e.contMDiffOn hinv (hsub hx) C u v hs
  have hcont : ContinuousOn f (Icc a T) :=
    (continuousOn_pullback_twoJet_time (uniqueDiffOn_Icc (ha.trans_lt haT)) F
      e.open_source e.contMDiffOn (hsub hx)).mono (Icc_subset_Icc ha le_rfl)
  have hstart : f a ∈ collarJetRegion C u v :=
    hinitialMargin J hJ _ (hnear.trans (min_le_right _ _))
  have hkeep : MapsTo f (Icc a T) (collarJetRegion C u v) := by
    apply hcont.mapsTo_of_open_prefix (isOpen_collarJetRegion C u v) hstart
    intro c hc hprior
    have hc0 : 0 < c := ha.trans_lt hc.1
    have hcurv := hcontrolled c hc (fun s hs => hplane s (hprior hs))
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
      (Icc_subset_Icc le_rfl hc.2) ordConnected_Icc (Icc_infinite hc0).nontrivial
    have hshift : a + (c - a) = c := by ring
    have hlast := hpreserve (fun s => (F.metric (a + s)).pullbackCoefficients e) x J hJ
      (by simpa only [add_zero] using hnear.trans (min_le_left _ _))
      (c - a) (sub_nonneg.mpr hc.1.le) (by linarith only [hc.2, hTtau])
      (fun j hj => by
        have h := (hmod M hc0 (hc.2.trans hTH) G e hcurv hinitial hV hsub hcompact
          hinside hlower hupper hjets j hj x hx).2 a ⟨ha, hc.1.le⟩ c ⟨hc0.le, le_rfl⟩
        simpa only [G, Poincare.Geometry.RicciFlow.Harnack.restrictFlow, add_zero,
          hshift, abs_of_nonneg (sub_nonneg.mpr hc.1.le)] using h)
    simpa only [hshift] using hlast
  refine ⟨fun t ht => hkeep ht, ?_⟩
  exact hcontrolled T ⟨haT, le_rfl⟩ (fun s hs => hplane s (hkeep ⟨hs.1, hs.2.le⟩))

end PoincareConjecture.M44
