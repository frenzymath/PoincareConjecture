import PoincareConjecture.Proofs.M44.Mathlib.FirstExit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StandardCollar
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance stoppedCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance stoppedCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance stoppedTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance stoppedTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_stopped_local_collar (P : M44CapPersistencePredecessors.{u})
    (C : ℝ) (u v : E) {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C u v)
    {K H r a b Z : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 ≤ b) (hZ : 1 ≤ Z) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ {T : ℝ}, 0 < T → T ≤ H → T ≤ tau → ∀ F : RicciFlow 3 M (Icc 0 T),
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞,
      (∀ j ≤ 2, ∀ y ∈ e.target, (F.connection 0).curvatureDerivativeNorm j y ≤ K) →
      ∀ {V : Set E}, IsOpen V → V ⊆ e.source →
      (∀ y ∈ V, IsCompact (closure ((F.metric 0).ball (e y) r))) →
      (∀ y ∈ V, closure ((F.metric 0).ball (e y) r) ⊆ e.target) →
      (∀ y ∈ V, ∀ w, a * ‖w‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e y w w) →
      (∀ y ∈ V, ∀ w, (F.metric 0).pullbackCoefficients e y w w ≤ b * ‖w‖ ^ 2) →
      (∀ y ∈ V, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) y‖ ≤ Z) →
      ∀ x ∈ V, ∀ J ∈ model,
      ‖metricTwoJet ((F.metric 0).pullbackCoefficients e) x - J‖ ≤ delta →
      (∀ c ∈ Ioc (0 : ℝ) T,
        (∀ s ∈ Ico (0 : ℝ) c, ∃ p q : TangentSpace (𝓡 3) (e x),
          LeviCivitaData.IsOrthonormalPair (F.metric s) (e x) p q ∧
          (F.connection s).sectionalCurvature (e x) p q <
            C⁻¹ * (F.connection s).scalarCurvature (e x)) →
        ∀ s ∈ Icc (0 : ℝ) c, ∀ y ∈ e.target, (F.connection s).curvatureTensorNorm y ≤ K) →
      (∀ t ∈ Icc (0 : ℝ) T,
        metricTwoJet ((F.metric t).pullbackCoefficients e) x ∈ collarJetRegion C u v) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ e.target, (F.connection t).curvatureTensorNorm y ≤ K) := by
  obtain ⟨_, L, _, hL, hmod⟩ := exists_local_coordinate_modulus P 2 hK hH hr ha hb hZ
  obtain ⟨d, tau, hd, htau, hpreserve⟩ :=
    exists_collar_jet_time_margin C u v hmodel hmargin hL
  obtain ⟨d0, hd0, hinitialMargin⟩ := exists_uniform_collar_jet_margin C u v hmodel hmargin
  refine ⟨min d d0, tau, lt_min hd hd0, htau, ?_⟩
  intro M _ _ _ _ _ T hT hTH hTtau F e hinitial V hV hsub hcompact hinside
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
  have hcont : ContinuousOn f (Icc (0 : ℝ) T) :=
    continuousOn_pullback_twoJet_time (uniqueDiffOn_Icc hT) F e.open_source e.contMDiffOn
      (hsub hx)
  have hzero : f 0 ∈ collarJetRegion C u v :=
    hinitialMargin J hJ _ (hnear.trans (min_le_right _ _))
  have hkeep : MapsTo f (Icc (0 : ℝ) T) (collarJetRegion C u v) := by
    apply hcont.mapsTo_of_open_prefix (isOpen_collarJetRegion C u v) hzero
    intro c hc hprior
    have hcurv := hcontrolled c hc (fun s hs => hplane s (hprior hs))
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
      (Icc_subset_Icc le_rfl hc.2) ordConnected_Icc
      (show (Icc (0 : ℝ) c).Nontrivial from ⟨0, ⟨le_rfl, hc.1.le⟩,
        c, ⟨hc.1.le, le_rfl⟩, hc.1.ne⟩)
    apply hpreserve (fun s => (F.metric s).pullbackCoefficients e) x J hJ
      (hnear.trans (min_le_left _ _)) c hc.1.le (hc.2.trans hTtau)
    intro j hj
    have h := (hmod M hc.1 (hc.2.trans hTH) G e hcurv hinitial hV hsub hcompact
      hinside hlower hupper hjets j hj x hx).2 0 ⟨le_rfl, hc.1.le⟩ c ⟨hc.1.le, le_rfl⟩
    simpa only [G, Poincare.Geometry.RicciFlow.Harnack.restrictFlow, sub_zero,
      abs_of_nonneg hc.1.le] using h
  refine ⟨fun t ht => hkeep ht, ?_⟩
  exact hcontrolled T ⟨hT, le_rfl⟩ (fun s hs => hplane s (hkeep ⟨hs.1, hs.2.le⟩))

end PoincareConjecture.M44
