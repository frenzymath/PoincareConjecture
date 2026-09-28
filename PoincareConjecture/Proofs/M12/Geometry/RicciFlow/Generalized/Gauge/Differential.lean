import PoincareConjecture.Statements.M12MovingGaugeTheory









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

private lemma movingGauge_mfderiv_time_base
    (e : MovingSpacetimeGauge F T C) (t : T.Point) (x : C) :
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (T.positiveTangent t, 0) =
      mfderiv (𝓡∂ 1) (spacetimeModel n)
        (fun s : T.Point ↦ e.toSpacetime (s, x)) t (T.positiveTangent t) := by
  letI : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  letI : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  have hprod := mfderiv_prod_eq_add_apply
    (p := (t, x))
    (e.smooth.mdifferentiableAt (by simp))
    (v := (T.positiveTangent t, 0))
  calc
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (T.positiveTangent t, 0) =
      mfderiv (𝓡∂ 1) (spacetimeModel n)
        (fun s : T.Point ↦ e.toSpacetime (s, x)) t (T.positiveTangent t) +
        mfderiv (𝓡 n) (spacetimeModel n)
          (fun y : C ↦ e.toSpacetime (t, y)) x 0 := hprod
    _ = mfderiv (𝓡∂ 1) (spacetimeModel n)
        (fun s : T.Point ↦ e.toSpacetime (s, x)) t (T.positiveTangent t) := by
      rw [map_zero, add_zero]

private lemma movingGauge_mfderiv_prod
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) (a : ℝ) (u : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u) =
      a • movingGaugeTimeVelocity e t x +
        (G.spatialTangentEquiv t x u).val := by
  letI : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  letI : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  have hprod := mfderiv_prod_eq_add_apply
    (p := (t, x))
    (e.smooth.mdifferentiableAt (by simp))
    (v := (a • T.positiveTangent t, u))
  have htime :
      mfderiv (𝓡∂ 1) (spacetimeModel n)
          (fun s : T.Point ↦ e.toSpacetime (s, x)) t
          (a • T.positiveTangent t) =
        a • movingGaugeTimeVelocity e t x := by
    rw [map_smul]
    simpa only [movingGaugeTimeVelocity] using
      congrArg (fun z => a • z) (movingGauge_mfderiv_time_base e t x).symm
  calc
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u) =
      mfderiv (𝓡∂ 1) (spacetimeModel n)
        (fun s : T.Point ↦ e.toSpacetime (s, x)) t
          (a • T.positiveTangent t) +
        mfderiv (𝓡 n) (spacetimeModel n)
          (fun y : C ↦ e.toSpacetime (t, y)) x u := hprod
    _ = a • movingGaugeTimeVelocity e t x +
        (G.spatialTangentEquiv t x u).val := by
      rw [htime, G.spatialTangentEquiv_eq]



lemma compatibleMovingGaugeDrift_zero
    (e : CompatibleSpacetimeCylinder F T C) (G : SpacetimeCylinderMetric e)
    (t : T.Point) (x : C) :
    movingGaugeDrift G.toMovingSpacetimeGaugeGeometry t x = 0 := by
  let e' := e.toMovingSpacetimeGauge
  let G' := G.toMovingSpacetimeGaugeGeometry
  have hvelocity : movingGaugeTimeVelocity e' t x =
      F.timeVector (e.toSpacetime (t, x)) := by
    unfold movingGaugeTimeVelocity
    rw [movingGauge_mfderiv_time_base e' t x]
    exact e.worldline_derivative t x
  have hprojection : F.horizontalProjection (e.toSpacetime (t, x))
      (F.timeVector (e.toSpacetime (t, x))) = 0 := by
    apply Subtype.ext
    rw [F.horizontalProjection_eq]
    change F.timeVector (e.toSpacetime (t, x)) -
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
        F.timeFunction (e.toSpacetime (t, x))
          (F.timeVector (e.toSpacetime (t, x)))) •
        F.timeVector (e.toSpacetime (t, x)) = 0
    have hnorm : (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
        F.timeFunction (e.toSpacetime (t, x))
          (F.timeVector (e.toSpacetime (t, x)))) = 1 :=
      F.timeVector_normalized (e.toSpacetime (t, x))
    rw [hnorm]
    change F.timeVector (e.toSpacetime (t, x)) -
      (1 : ℝ) • F.timeVector (e.toSpacetime (t, x)) = 0
    simp
  change (G'.spatialTangentEquiv t x).symm
      (-F.horizontalProjection (e.toSpacetime (t, x))
        (movingGaugeTimeVelocity e' t x)) = 0
  rw [hvelocity, hprojection]
  rw [neg_zero]
  change (G'.spatialTangentEquiv t x).symm
      (0 : F.Horizontal (e.toSpacetime (t, x))) = 0
  exact (G'.spatialTangentEquiv t x).symm.map_zero

lemma movingGauge_projection_eq
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) (a : ℝ) (u : TangentSpace (𝓡 n) x) :
    F.horizontalProjection (e.toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u)) =
      G.spatialTangentEquiv t x (u - a • movingGaugeDrift G t x) := by
  have hprod := movingGauge_mfderiv_prod e G t x a u
  have hdrift : G.spatialTangentEquiv t x (movingGaugeDrift G t x) =
      -F.horizontalProjection (e.toSpacetime (t, x))
        (movingGaugeTimeVelocity e t x) := by
    unfold movingGaugeDrift
    exact (G.spatialTangentEquiv t x).apply_symm_apply _
  let p : F.Point := e.toSpacetime (t, x)
  let P : TangentSpace (spacetimeModel n) p →L[ℝ] F.Horizontal p :=
    F.horizontalProjection p
  let E : TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal p :=
    G.spatialTangentEquiv t x
  have hprod' :
      mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u) =
      a • movingGaugeTimeVelocity e t x + (E u).val := by
    simpa only [E] using hprod
  have hdrift' : E (movingGaugeDrift G t x) =
      -P (movingGaugeTimeVelocity e t x) := by
    dsimp [E, P, p]
    exact hdrift
  change P
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u)) =
      E (u - a • movingGaugeDrift G t x)
  calc
    P
        (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
          (a • T.positiveTangent t, u)) =
      P
        (a • movingGaugeTimeVelocity e t x +
          (E u).val) := by rw [hprod']
    _ = a • P
          (movingGaugeTimeVelocity e t x) +
        E u := by
      rw [map_add, map_smul]
      rw [show P (E u).val = E u from F.horizontalProjection_identity p (E u)]
    _ = E u - a •
          (-P
            (movingGaugeTimeVelocity e t x)) := by
      rw [sub_eq_add_neg, smul_neg, neg_neg]
      abel
    _ = E (u - a • movingGaugeDrift G t x) := by
      rw [map_sub, map_smul, hdrift']

private lemma movingGauge_time_derivative
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction
      (e.toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (T.positiveTangent t, movingGaugeDrift G t x))) = 1 := by
  letI : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  letI : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  letI : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  letI : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  change (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) time
      (e.toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (T.positiveTangent t, movingGaugeDrift G t x))) = 1
  letI : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  letI : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  letI : NormedAddCommGroup
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  letI : NormedSpace ℝ
      (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n)))
  have hcomp := mfderiv_comp_apply (x := (t, x))
    (F.time_smooth.mdifferentiableAt (by simp))
    (e.smooth.mdifferentiableAt (by simp))
    (T.positiveTangent t, movingGaugeDrift G t x)
  have heq : time ∘ e.toSpacetime =
      (fun q : T.Point × C ↦ q.1.val) := by
    funext q
    exact e.time_eq q
  rw [heq] at hcomp
  have hcoord := mfderiv_prod_eq_add_apply
    (p := (t, x))
    (f := fun q : T.Point × C ↦ q.1.val)
    (T.inclusion_smooth.mdifferentiableAt (by simp) |>.comp
      (t, x) (mdifferentiableAt_fst (I := 𝓡∂ 1) (I' := 𝓡 n)))
    (v := (T.positiveTangent t, movingGaugeDrift G t x))
  have hconst :
      mfderiv (𝓡 n) 𝓘(ℝ) (fun _ : C ↦ (t.val : ℝ)) x
          (movingGaugeDrift G t x) = 0 := by
    have hzero := mfderiv_const (I := 𝓡 n) (I' := 𝓘(ℝ))
      (x := x) (c := (t.val : ℝ))
    have hzero_apply := congrArg
      (fun L => L (movingGaugeDrift G t x)) hzero
    simpa only [zero_apply] using hzero_apply
  have hcoord' :
      mfderiv (spacetimeModel n) 𝓘(ℝ)
          (fun q : T.Point × C ↦ q.1.val) (t, x)
            (T.positiveTangent t, movingGaugeDrift G t x) =
        mfderiv (𝓡∂ 1) 𝓘(ℝ)
          (fun s : T.Point ↦ s.val) t (T.positiveTangent t) := by
    calc
      mfderiv (spacetimeModel n) 𝓘(ℝ)
          (fun q : T.Point × C ↦ q.1.val) (t, x)
            (T.positiveTangent t, movingGaugeDrift G t x) =
        mfderiv (𝓡∂ 1) 𝓘(ℝ)
            (fun z : T.Point ↦ z.val) t (T.positiveTangent t) +
          mfderiv (𝓡 n) 𝓘(ℝ)
            (fun z : C ↦ t.val) x (movingGaugeDrift G t x) := hcoord
      _ = mfderiv (𝓡∂ 1) 𝓘(ℝ)
            (fun z : T.Point ↦ z.val) t (T.positiveTangent t) + 0 := by
        congr 1
      _ = mfderiv (𝓡∂ 1) 𝓘(ℝ)
            (fun s : T.Point ↦ s.val) t (T.positiveTangent t) := by
        simp
  have hinclusion :
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : T.Point → ℝ) t
          (T.positiveTangent t) = 1 := by
    rw [← T.inclusionDerivative_eq]
    exact (T.inclusionDerivative t).apply_symm_apply 1
  have hcoord_one :
      mfderiv (spacetimeModel n) 𝓘(ℝ)
          (fun q : T.Point × C ↦ q.1.val) (t, x)
            (T.positiveTangent t, movingGaugeDrift G t x) = 1 := by
    calc
      mfderiv (spacetimeModel n) 𝓘(ℝ)
          (fun q : T.Point × C ↦ q.1.val) (t, x)
            (T.positiveTangent t, movingGaugeDrift G t x) =
        mfderiv (𝓡∂ 1) 𝓘(ℝ)
            (fun s : T.Point ↦ s.val) t (T.positiveTangent t) := hcoord'
      _ = 1 := hinclusion
  have htimeEq :
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) time
        (e.toSpacetime (t, x))
        (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
          (T.positiveTangent t, movingGaugeDrift G t x))) =
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
        (fun q : T.Point × C ↦ q.1.val) (t, x)
          (T.positiveTangent t, movingGaugeDrift G t x)) := by
    rw [← hcomp]
  have hcoord_one' :
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
        (fun q : T.Point × C ↦ q.1.val) (t, x)
          (T.positiveTangent t, movingGaugeDrift G t x)) = 1 := hcoord_one
  exact htimeEq.trans hcoord_one'



lemma movingGauge_time_vector_eq
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) :
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
      (T.positiveTangent t, movingGaugeDrift G t x) =
      F.timeVector (e.toSpacetime (t, x)) := by
  letI : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  letI : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  letI : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  letI : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  let p : F.Point := e.toSpacetime (t, x)
  let w : TangentSpace (spacetimeModel n) p :=
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
      (T.positiveTangent t, movingGaugeDrift G t x)
  have hproj : F.horizontalProjection p w = 0 := by
    have h := movingGauge_projection_eq e G t x 1 (movingGaugeDrift G t x)
    have h' : F.horizontalProjection p w =
        G.spatialTangentEquiv t x
          (movingGaugeDrift G t x - 1 • movingGaugeDrift G t x) := by
      simpa [p, w] using h
    rw [h']
    apply Subtype.ext
    simp only [one_smul, sub_self, map_zero]
    rfl
  have htime :
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) time p w) = 1 := by
    change (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) F.timeFunction p w) = 1
    simpa [p, w] using movingGauge_time_derivative e G t x
  have hdecomp := F.tangent_decomposition p w
  rw [htime, hproj] at hdecomp
  simpa [p, w] using hdecomp

end
end PoincareConjecture
