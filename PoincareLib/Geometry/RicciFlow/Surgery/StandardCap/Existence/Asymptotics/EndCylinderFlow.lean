import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderRicci
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndPullbackFlow

/-!
# The genuine cylinder Ricci flow on the canonical reference end

Restrict the actual auxiliary ambient metric to the fixed canonical
reference domain. Its actual canonical connection has the proved end
Ricci tensor. The affine included-time metric pairing therefore satisfies
the Ricci-flow equation, including the initial endpoint. This is
Proposition 12.7, pp. 298-299 and canonical-cylinder-model.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

/-- The actual auxiliary metric restricted through the canonical
inclusion local diffeomorphism (Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderMetric (t : ℝ) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    RiemannianMetric 3 (endReferenceRegion e) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  exact (endCylinderAuxMetric e t).pullbackOfLocalDiffeomorph
    (Subtype.val : endReferenceRegion e → StandardCapSpace)
    (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (endReferenceRegion e)
      (endReferenceRegion_isOpen e) ∞)

/-- Exact total-time coefficients in the canonical tangent coordinates
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderMetric_inner :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (x : endReferenceRegion e) (u v : StandardCapSpace),
      (endCylinderMetric e t).inner x u v =
        endCylinderCoefficients e (endCylinderParameter t) x u v := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t x u v
  change (endCylinderAuxMetric e t).inner x
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : endReferenceRegion e → StandardCapSpace) x u)
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : endReferenceRegion e → StandardCapSpace) x v) = _
  rw [mfderiv_subtypeVal_singleton (endReferenceRegion_isOpen e)]
  rfl

/-- Restriction preserves joint included-time metric smoothness
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderMetric_smooth :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    RiemannianMetric.IsSmoothFamilyOn (endCylinderMetric e) (Ico 0 1) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  exact (endCylinderAuxMetric_smooth e).pullbackOfLocalDiffeomorph
    (Subtype.val : endReferenceRegion e → StandardCapSpace)
    (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (endReferenceRegion e)
      (endReferenceRegion_isOpen e) ∞)

/-- Every actual compatible canonical connection has the intrinsic
cylinder Ricci tensor on the reference region
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderMetric_ricci :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ) (D : LeviCivitaData (endCylinderMetric e t))
      (x : endReferenceRegion e) (u v : StandardCapSpace),
      D.ricci x u v = (g.inner x u v -
        fderiv ℝ (endExhaustion e) x u * fderiv ℝ (endExhaustion e) x v) / 2 := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t D x u v
  let DA := (endCylinderAuxMetric e t).euclideanLeviCivitaData
  have hi := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (endReferenceRegion e)
    (endReferenceRegion_isOpen e) ∞
  have hr := D.ricci_eq_of_local_isometry DA isOpen_univ hi.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x) u v
  rw [mfderiv_subtypeVal_singleton (endReferenceRegion_isOpen e)] at hr
  change D.ricci x u v = DA.ricci (x : StandardCapSpace) u v at hr
  rw [hr]
  obtain ⟨z, hz, hx⟩ := x.property
  have hh : 2 < z.2 := by have h := hz.2.1; linarith
  exact (congrArg (fun p : StandardCapSpace => DA.ricci p u v =
    (g.inner p u v - fderiv ℝ (endExhaustion e) p u *
      fderiv ℝ (endExhaustion e) p v) / 2) hx).mp
        (endCylinderAuxRicci_coordinate e t DA hh u v)

/-- The actual included-time metric pairing has its affine derivative,
including the one-sided initial endpoint
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderMetric_hasDerivWithinAt :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ), t ∈ Ico 0 1 → ∀ (x : endReferenceRegion e) (u v : StandardCapSpace),
      HasDerivWithinAt (fun s => (endCylinderMetric e s).inner x u v)
        (-g.inner x u v + fderiv ℝ (endExhaustion e) x u * fderiv ℝ (endExhaustion e) x v)
          (Ico 0 1) t := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t ht x u v
  let a : ℝ := g.inner x u v
  let b : ℝ := fderiv ℝ (endExhaustion e) x u * fderiv ℝ (endExhaustion e) x v
  have h := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const a).add
    ((hasDerivAt_id t).mul_const b)
  have hh : HasDerivWithinAt (fun s : ℝ => (1 - s) * a + s * b) (-a + b) (Ico 0 1) t := by
    convert! h.hasDerivWithinAt using 1
    ring
  apply hh.congr_of_mem _ ht
  intro s hs
  rw [endCylinderMetric_inner, endCylinderParameter, if_pos hs, endCylinderCoefficients_apply]

/-- The genuine shrinking-cylinder Ricci flow on the fixed canonical
reference end, with an actual constructed compatible connection
(Proposition 12.7, pp. 298-299). -/
noncomputable def endCylinderFlow :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    RicciFlow 3 (endReferenceRegion e) (Ico 0 1) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  exact {
    metric := endCylinderMetric e
    connection := fun t => RiemannianMetric.canonicalMetricLeviCivitaData
      (endReferenceRegion e) (endReferenceRegion_isOpen e) (endCylinderMetric e t)
    interval := ordConnected_Ico
    nontrivial := ⟨0, by norm_num, 1 / 2, by norm_num, by norm_num⟩
    smooth := endCylinderMetric_smooth e
    equation := fun t ht x u v => by
      rw [endCylinderMetric_ricci]
      convert! endCylinderMetric_hasDerivWithinAt e t ht x u v using 1
      ring }

end PoincareMT.M34
