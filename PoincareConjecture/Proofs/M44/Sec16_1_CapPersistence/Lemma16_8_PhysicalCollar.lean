import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CollarJetMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_LocalCoordinateModulus
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance physicalCollarCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance physicalCollarCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance physicalCollarTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance physicalCollarTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem exists_collar_plane_of_pullback_twoJet
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) (C : ℝ) (u v : E)
    (hJ : metricTwoJet (g.pullbackCoefficients f) x ∈ collarJetRegion C u v) :
    ∃ p q : TangentSpace (𝓡 3) (f x), LeviCivitaData.IsOrthonormalPair g (f x) p q ∧
      D.sectionalCurvature (f x) p q < C⁻¹ * D.scalarCurvature (f x) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ a b => g.symm (f y) _ _)
      (fun y hy a ha => by
        apply g.pos (f y)
        intro hz
        apply ha
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  have htwo : metricTwoJet gE.euclideanCoefficients x =
      metricTwoJet (g.pullbackCoefficients f) x := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  obtain ⟨p, q, horth, hmargin⟩ := exists_collar_plane_of_twoJet DE x C u v (htwo ▸ hJ)
  have hgeom (y : E) (hy : y ∈ V) (a b : E) :
      gE.inner y a b = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b) :=
    congrArg (fun B => B a b) (hmetric y hy)
  let L := mfderiv (𝓡 3) (𝓡 3) f x
  have hscalar := (scalar_ricciNormSq_eq_of_metric_pullback DE D
    (hf.contMDiffAt (hU.mem_nhds hx))
    (eventually_of_mem (hV.mem_nhds hxV) (fun y hy => hinv y (hVU hy)))
    (eventually_of_mem (hV.mem_nhds hxV) hgeom)).1
  have hsectional : DE.sectionalCurvature x p q = D.sectionalCurvature (f x) (L p) (L q) := by
    unfold LeviCivitaData.sectionalCurvature
    rw [DE.curvatureTensor_eq_of_local_isometry D hV (hf.mono hVU) hgeom hxV,
      hgeom x hxV p p, hgeom x hxV q q, hgeom x hxV p q]
  refine ⟨L p, L q, ?_, ?_⟩
  · exact ⟨(hgeom x hxV p p).symm.trans horth.1,
      (hgeom x hxV q q).symm.trans horth.2.1,
      (hgeom x hxV p q).symm.trans horth.2.2⟩
  · rw [← hsectional, hscalar]
    exact hmargin





theorem exists_local_collar_preservation (P : M44CapPersistencePredecessors.{u})
    (C : ℝ) (u v : E) {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C u v)
    {K H r a b Z : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 ≤ b) (hZ : 1 ≤ Z) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ {T : ℝ}, 0 < T → T ≤ H → T ≤ tau → ∀ F : RicciFlow 3 M (Icc 0 T),
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞,
      (∀ t ∈ Icc 0 T, ∀ x ∈ e.target, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ 2, ∀ x ∈ e.target, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ {V : Set E}, IsOpen V → V ⊆ e.source →
      (∀ x ∈ V, IsCompact (closure ((F.metric 0).ball (e x) r))) →
      (∀ x ∈ V, closure ((F.metric 0).ball (e x) r) ⊆ e.target) →
      (∀ x ∈ V, ∀ w, a * ‖w‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e x w w) →
      (∀ x ∈ V, ∀ w, (F.metric 0).pullbackCoefficients e x w w ≤ b * ‖w‖ ^ 2) →
      (∀ x ∈ V, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) x‖ ≤ Z) →
      ∀ x ∈ V, ∀ J ∈ model,
      ‖metricTwoJet ((F.metric 0).pullbackCoefficients e) x - J‖ ≤ delta →
      ∀ t ∈ Icc 0 T, ∃ p q : TangentSpace (𝓡 3) (e x),
        LeviCivitaData.IsOrthonormalPair (F.metric t) (e x) p q ∧
          (F.connection t).sectionalCurvature (e x) p q <
            C⁻¹ * (F.connection t).scalarCurvature (e x) := by
  obtain ⟨_, L, _, hL, hmod⟩ := exists_local_coordinate_modulus P 2 hK hH hr ha hb hZ
  obtain ⟨delta, tau, hdelta, htau, hkeep⟩ :=
    exists_collar_jet_time_margin C u v hmodel hmargin hL
  refine ⟨delta, tau, hdelta, htau, ?_⟩
  intro M _ _ _ _ _ T hT hTH hTtau F e hcurv hinitial V hV hsub hcompact hinside
    hlower hupper hjets x hx J hJ hnear t ht
  have hjet : metricTwoJet ((F.metric t).pullbackCoefficients e) x ∈
      collarJetRegion C u v := by
    apply hkeep (fun s => (F.metric s).pullbackCoefficients e) x J hJ hnear t ht.1
      (ht.2.trans hTtau)
    intro j hj
    have h := (hmod M hT hTH F e hcurv hinitial hV hsub hcompact hinside
      hlower hupper hjets j hj x hx).2 0 ⟨le_rfl, hT.le⟩ t ht
    simpa only [sub_zero, abs_of_nonneg ht.1] using h
  have hinv : ∀ y ∈ e.source, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible := by
    intro y hy
    have hd := e.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy
    exact ⟨hd.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  exact exists_collar_plane_of_pullback_twoJet (F.metric t) (F.connection t)
    e.open_source e.contMDiffOn hinv (hsub hx) C u v hjet

end PoincareConjecture.M44
