import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StandardCollar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance globalCollarCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance globalCollarCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance globalCollarTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance globalCollarTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem collarJetRegion_of_pullback
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E E ∞) {x : E} (hx : x ∈ f.source)
    (C : ℝ) (u v : E)
    (hJ : metricTwoJet (g.pullbackCoefficients f) x ∈ collarJetRegion C u v) :
    metricTwoJet g.euclideanCoefficients (f x) ∈ collarJetRegion C
      (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v) := by
  have hinv : ∀ y ∈ f.source, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible := by
    intro y hy
    exact ⟨(f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  obtain ⟨gE, DE, V, hV, hxV, hsub, hmetric⟩ :=
    RiemannianMetric.exists_local_realization f.open_source hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hy))).contDiffWithinAt)
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
  have hgeom (y : E) (hy : y ∈ V) (a b : E) :
      gE.inner y a b = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b) := congrArg (fun B => B a b) (hmetric y hy)
  have hscalar := (scalar_ricciNormSq_eq_of_metric_pullback DE D
    (f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hx))
    (eventually_of_mem (hV.mem_nhds hxV) (fun y hy => hinv y (hsub hy)))
    (eventually_of_mem (hV.mem_nhds hxV) hgeom)).1
  have hsectional : DE.sectionalCurvature x u v =
      D.sectionalCurvature (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
        (mfderiv (𝓡 3) (𝓡 3) f x v) := by
    unfold LeviCivitaData.sectionalCurvature
    rw [DE.curvatureTensor_eq_of_local_isometry D hV (f.contMDiffOn.mono hsub) hgeom hxV,
      hgeom x hxV u u, hgeom x hxV v v, hgeom x hxV u v]
  have hlocal : metricTwoJet gE.euclideanCoefficients x ∈ collarJetRegion C u v := htwo ▸ hJ
  have hlocalMargin := hlocal.2.2
  simp only [collarJetMargin, jetScalarCurvature_metricTwoJet DE,
    jetCurvature_metricTwoJet DE] at hlocalMargin
  have hmargin : DE.sectionalCurvature x u v < C⁻¹ * DE.scalarCurvature x :=
    sub_pos.mp hlocalMargin
  rw [hsectional, ← hscalar] at hmargin
  refine ⟨g.inner_isInvertible (f x), hJ.2.1, ?_⟩
  simp only [collarJetMargin, jetScalarCurvature_metricTwoJet D, jetCurvature_metricTwoJet D]
  exact sub_pos.mpr hmargin




theorem continuousOn_euclidean_twoJet_time {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    (F : RicciFlow 3 E J) (x : E) :
    ContinuousOn (fun t => metricTwoJet (F.metric t).euclideanCoefficients x) J := by
  have hid (g : RiemannianMetric 3 E) : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext y v w
    simp only [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  have h := continuousOn_pullback_twoJet_time hJ F isOpen_univ
    (contMDiff_id.contMDiffOn (s := univ)) (mem_univ x)
  simpa only [hid] using h




theorem exists_global_standard_collar {g0 : StandardInitialMetric}
    (S : RepairedStandardCapExistenceData g0) {C theta : ℝ}
    (hC : 0 < C) (htheta0 : 0 ≤ theta) (htheta : theta < 1) :
    ∃ x u v : E,
      IsCompact ((fun t => metricTwoJet (S.flow.metric t).euclideanCoefficients x) ''
        Icc (0 : ℝ) theta) ∧
      ∀ t ∈ Icc (0 : ℝ) theta,
        metricTwoJet (S.flow.metric t).euclideanCoefficients x ∈ collarJetRegion C u v := by
  obtain ⟨f, hx, _hcompact, hmargin⟩ := exists_standard_collar_chart S hC htheta0 htheta
  let u := mfderiv (𝓡 3) (𝓡 3) f 0 (EuclideanSpace.basisFun (Fin 3) ℝ 0)
  let v := mfderiv (𝓡 3) (𝓡 3) f 0 (EuclideanSpace.basisFun (Fin 3) ℝ 2)
  have hcontinuous := continuousOn_euclidean_twoJet_time
    (uniqueDiffOn_Ico 0 S.flow.base.lifetime) S.flow.base.flow (f 0)
  have hsub : Icc (0 : ℝ) theta ⊆ Ico (0 : ℝ) S.flow.base.lifetime := by
    rw [S.lifetime_one]
    exact fun _ ht => ⟨ht.1, ht.2.trans_lt htheta⟩
  refine ⟨f 0, u, v, isCompact_Icc.image_of_continuousOn (hcontinuous.mono hsub), ?_⟩
  intro t ht
  exact collarJetRegion_of_pullback (S.flow.metric t) (S.flow.connection t) f hx C
    (EuclideanSpace.basisFun (Fin 3) ℝ 0) (EuclideanSpace.basisFun (Fin 3) ℝ 2) (hmargin t ht)

end PoincareConjecture.M44
