import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Differential
import PoincareConjecture.Proofs.M12.Geometry.Manifold.VectorField.Product
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.TimeBracket

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter Bundle

universe u v

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

theorem movingGauge_mfderiv_isInvertible (e : MovingSpacetimeGauge F T C)
    (p : T.Point × C) :
    (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime p).IsInvertible := by
  let L : SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n :=
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime p
  have hL : Function.Bijective L :=
    ⟨e.differential_injective p,
      (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp
        (e.differential_injective p)⟩
  exact ⟨ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2), rfl⟩

theorem movingGauge_mfderiv_spatial (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e) (t : T.Point) (x : C)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x) (0, v) =
      (G.spatialTangentEquiv t x v).val := by
  let : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  let : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let : NormedAddCommGroup
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  let : NormedSpace ℝ
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  have h := mfderiv_prod_eq_add_apply (p := (t, x))
    (e.smooth.mdifferentiableAt (by simp)) (v := (0, v))
  simpa only [map_zero, zero_add, G.spatialTangentEquiv_eq] using h

theorem movingGauge_mpullback_timeVector (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e) :
    VectorField.mpullback (spacetimeModel n) (spacetimeModel n) e.toSpacetime
      (show (p : F.Point) → TangentSpace (spacetimeModel n) p from F.timeVector) =
      fun p : T.Point × C => (T.positiveTangent p.1, movingGaugeDrift G p.1 p.2) := by
  funext p
  rw [VectorField.mpullback_apply,
    ← movingGauge_time_vector_eq e G p.1 p.2]
  exact (movingGauge_mfderiv_isInvertible e p).inverse_apply_self _

theorem movingGauge_mpullback_horizontalSection (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e) (V : HorizontalSection F) :
    VectorField.mpullback (spacetimeModel n) (spacetimeModel n) e.toSpacetime
      (horizontalSectionVectorField F V) =
      fun p : T.Point × C => (0, pullbackHorizontalSection G V p.1 p.2) := by
  funext p
  have h := movingGauge_mfderiv_spatial e G p.1 p.2
    (pullbackHorizontalSection G V p.1 p.2)
  simp only [pullbackHorizontalSection, ContinuousLinearEquiv.apply_symm_apply] at h
  rw [VectorField.mpullback_apply]
  change (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime p).inverse
    (V (e.toSpacetime p)).val = _
  rw [← h]
  exact (movingGauge_mfderiv_isInvertible e p).inverse_apply_self _

theorem movingGauge_liftedDrift_smooth
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e) :
    ContMDiff (spacetimeModel n) (spacetimeModel n).tangent ∞
      (fun p : T.Point × C => (⟨p, (T.positiveTangent p.1, movingGaugeDrift G p.1 p.2)⟩ :
        TangentBundle (spacetimeModel n) (T.Point × C))) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hs := F.timeVector_smooth.mpullback_vectorField e.smooth
    (movingGauge_mfderiv_isInvertible e) (by simp)
  simpa only [movingGauge_mpullback_timeVector e G] using hs

theorem movingGauge_liftedSection_smoothAt
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (p : T.Point × C)
    (hp : e.toSpacetime p ∈ O) :
    ContMDiffAt (spacetimeModel n) (spacetimeModel n).tangent ∞
      (fun q : T.Point × C => (⟨q, (0, pullbackHorizontalSection G V q.1 q.2)⟩ :
        TangentBundle (spacetimeModel n) (T.Point × C))) p := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hs := (hV.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mpullback_vectorField_preimage
    (e.smooth p) (movingGauge_mfderiv_isInvertible e p) (by simp)
  simpa only [movingGauge_mpullback_horizontalSection e G V] using hs

theorem movingGauge_pullbackHorizontalSection_smoothAt
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (p : T.Point × C)
    (hp : e.toSpacetime p ∈ O) :
    ContMDiffAt (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : T.Point × C => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) q.2 (pullbackHorizontalSection G V q.1 q.2)) p := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hs := movingGauge_liftedSection_smoothAt e G V O hO hV p hp
  have hproj := (contMDiff_equivTangentBundleProd
    (I := 𝓡∂ 1) (M := T.Point) (I' := 𝓡 n) (M' := C) (n := ∞)).snd
  exact (hproj.contMDiffAt.comp p hs)

theorem movingGauge_horizontalTimeBracket_pullback
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (t : T.Point) (x : C)
    (hp : e.toSpacetime (t, x) ∈ O) :
    (0, (G.spatialTangentEquiv t x).symm
      (horizontalTimeBracket F V (e.toSpacetime (t, x)))) =
      VectorField.mlieBracket (spacetimeModel n)
        (fun p : T.Point × C => (T.positiveTangent p.1, movingGaugeDrift G p.1 p.2))
        (fun p : T.Point × C => (0, pullbackHorizontalSection G V p.1 p.2)) (t, x) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  let : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) (T.Point × C) := by
    simp only [minSmoothness_of_isRCLikeNormedField, spacetimeModel]
    infer_instance
  let : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) F.Point := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hb := VectorField.mpullback_mlieBracket
    ((F.timeVector_smooth (e.toSpacetime (t, x))).mdifferentiableAt (by simp))
    ((hV.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))
    (e.smooth (t, x)) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  rw [movingGauge_mpullback_timeVector e G,
    movingGauge_mpullback_horizontalSection e G V] at hb
  rw [VectorField.mpullback_apply, ← horizontalTimeBracket_val hO hV hp] at hb
  have hs := movingGauge_mfderiv_spatial e G t x
    ((G.spatialTangentEquiv t x).symm (horizontalTimeBracket F V (e.toSpacetime (t, x))))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hs
  rw [← hs] at hb
  simpa only [ContinuousLinearEquiv.apply_symm_apply,
    (movingGauge_mfderiv_isInvertible e (t, x)).inverse_apply_self] using hb

theorem movingGauge_drift_bracket_eq
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (hW : ContMDiff (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : T.Point × C => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        q.2 (movingGaugeDrift G q.1 q.2)))
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (t : T.Point) (x : C)
    (hp : e.toSpacetime (t, x) ∈ O) :
    VectorField.mlieBracket (𝓡 n) (movingGaugeDrift G t)
      (pullbackHorizontalSection G V t) x =
      (c t.val).connection (pullbackHorizontalSection G V t) x (movingGaugeDrift G t x) -
        (c t.val).connection (movingGaugeDrift G t) x (pullbackHorizontalSection G V t x) := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  apply ((c t.val).connection.torsion_eq_zero_iff.mp (c t.val).torsion_eq_zero _ _).symm
  · exact ((hW (t, x)).comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt
      (by simp)
  · exact ((movingGauge_pullbackHorizontalSection_smoothAt e G V O hO hV (t, x) hp).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)

theorem movingGaugeSectionTimeDerivative_eq_model
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (t : T.Point) (x : C)
    (hp : e.toSpacetime (t, x) ∈ O) :
    movingGaugeSectionTimeDerivative G V t x =
      mfderiv (𝓡∂ 1) (𝓡 n)
        (fun s : T.Point => (show EuclideanSpace ℝ (Fin n) from pullbackHorizontalSection G V s x))
        t (T.positiveTangent t) := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C → Type _) :=
    ⟨(G.metric t.val).toRiemannianMetric⟩
  let L : TangentSpace (𝓡 n) x ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearEquivAt
      ℝ x (mem_baseSet_trivializationAt _ _ x)
  have hL (w : TangentSpace (𝓡 n) x) : L w = (show EuclideanSpace ℝ (Fin n) from w) := by
    dsimp only [L]
    rw [Trivialization.coe_continuousLinearEquivAt_eq,
      TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ x),
      mfderiv_extChartAt_self]
    rfl
  have hLsymm (w : EuclideanSpace ℝ (Fin n)) : L.symm w = (show TangentSpace (𝓡 n) x from w) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hL (L.symm w)).symm
  have hs := (movingGauge_pullbackHorizontalSection_smoothAt e G V O hO hV (t, x) hp).comp t
    (contMDiffAt_id.prodMk contMDiffAt_const)
  have hraw : ContMDiffAt (𝓡∂ 1) (𝓡 n) ∞
      (fun s : T.Point => (show EuclideanSpace ℝ (Fin n) from pullbackHorizontalSection G V s x)) t := by
    have hc := (Bundle.contMDiffAt_totalSpace.mp hs).2
    change ContMDiffAt (𝓡∂ 1) (𝓡 n) ∞
      (fun s : T.Point => L (pullbackHorizontalSection G V s x)) t at hc
    simpa only [hL] using hc
  have hcomp := mfderiv_comp_apply (x := t)
    L.symm.differentiableAt.mdifferentiableAt
    (hraw.mdifferentiableAt (by simp)) (T.positiveTangent t)
  have hfun : L.symm ∘
      (fun s : T.Point => (show EuclideanSpace ℝ (Fin n) from pullbackHorizontalSection G V s x)) =
      (fun s : T.Point => pullbackHorizontalSection G V s x) := by
    funext s
    exact hLsymm _
  rw [hfun, mfderiv_eq_fderiv, L.symm.fderiv] at hcomp
  change mfderiv (𝓡∂ 1) 𝓘(ℝ, TangentSpace (𝓡 n) x)
      (fun s : T.Point => pullbackHorizontalSection G V s x) t (T.positiveTangent t) =
    L.symm (mfderiv (𝓡∂ 1) (𝓡 n)
      (fun s : T.Point => (show EuclideanSpace ℝ (Fin n) from pullbackHorizontalSection G V s x))
      t (T.positiveTangent t)) at hcomp
  rw [hLsymm] at hcomp
  exact hcomp

theorem movingGauge_horizontalTimeBracket_eq
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (hW : ContMDiff (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : T.Point × C => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        q.2 (movingGaugeDrift G q.1 q.2)))
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (t : T.Point) (x : C)
    (hp : e.toSpacetime (t, x) ∈ O) :
    horizontalTimeBracket F V (e.toSpacetime (t, x)) =
      G.spatialTangentEquiv t x
        (movingGaugeSectionTimeDerivative G V t x +
          (c t.val).connection (pullbackHorizontalSection G V t) x (movingGaugeDrift G t x) -
          (c t.val).connection (movingGaugeDrift G t) x (pullbackHorizontalSection G V t x)) := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hb := congrArg Prod.snd (movingGauge_horizontalTimeBracket_pullback e G V O hO hV t x hp)
  have hs := Poincare.Manifold.VectorField.mlieBracket_prod_snd T.positiveTangent (movingGaugeDrift G)
    (pullbackHorizontalSection G V) (t, x)
    (movingGauge_liftedDrift_smooth e G (t, x))
    (movingGauge_liftedSection_smoothAt e G V O hO hV (t, x) hp)
  apply (G.spatialTangentEquiv t x).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have h := hb.trans hs
  rw [← movingGaugeSectionTimeDerivative_eq_model e G V O hO hV t x hp,
    movingGauge_drift_bracket_eq e G c hW V O hO hV t x hp] at h
  simpa only [add_sub_assoc] using h

end

end PoincareConjecture
