import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



noncomputable def modifiedEndDoublePieceMetric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R) :
    let := endDoublePieceChartedSpace e hR
    let := endDoublePiece_isManifold e hR
    RiemannianMetric 3 (EndDoublePiece e R) := by
  let := endDoublePieceChartedSpace e hR
  let := endDoublePiece_isManifold e hR
  exact h.pullbackOfLocalDiffeomorph Subtype.val
    (endDoublePiece_subtypeVal_isLocalDiffeomorph e hR)



theorem modifiedEndDoublePieceMetric_inner (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R) :
    let := endDoublePieceChartedSpace e hR
    let := endDoublePiece_isManifold e hR
    ∀ (x : EndDoublePiece e R) (u v : TangentSpace (𝓡 3) x),
      (modifiedEndDoublePieceMetric e h hR).inner x u v = h.inner (x : StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) := by
  let := endDoublePieceChartedSpace e hR
  let := endDoublePiece_isManifold e hR
  dsimp only
  intro x u v
  rfl



theorem modifiedEndDoubleMetrics_compatible (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R)
    (hagrees : EqOn h.euclideanCoefficients g.euclideanCoefficients (endDoubleCollar e R)) :
    let := endDoublePiece_nonempty e hR
    CompatibleMetrics (fun _ : Bool => endTruncation e (R + 1))
      (fun _ => endTruncation_isOpen e (show 0 ≤ R + 1 by linarith))
      (endDoubleOverlap e hR) (fun _ => modifiedEndDoublePieceMetric e h hR) := by
  let := endDoublePiece_nonempty e hR
  let := endDoublePieceChartedSpace e hR
  let := endDoublePiece_isManifold e hR
  have heq (x : EndDoublePiece e R) (hx : (x : StandardCapSpace) ∈ endDoubleCollar e R)
      (u v : TangentSpace (𝓡 3) x) :
      (modifiedEndDoublePieceMetric e h hR).inner x u v =
        (endDoublePieceMetric e hR).inner x u v := by
    rw [modifiedEndDoublePieceMetric_inner, endDoublePieceMetric_inner]
    exact congrArg (fun B => B (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u)
      (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v)) (hagrees hx)
  dsimp only [CompatibleMetrics]
  intro i j x hx u v
  by_cases hij : i = j
  · subst j
    rw [(endDoubleOverlap e hR).self]
    change (modifiedEndDoublePieceMetric e h hR).inner x u v =
      (modifiedEndDoublePieceMetric e h hR).inner x
        (mfderiv (𝓡 3) (𝓡 3) id x u) (mfderiv (𝓡 3) (𝓡 3) id x v)
    rw [mfderiv_id]
    rfl
  · have ht : (endDoubleOverlap e hR).transition i j = endDoubleTransition e hR :=
      twoPieceOverlap_transition_ne _ _ hij
    rw [ht] at hx ⊢
    have hxval : (x : StandardCapSpace) ∈ endDoubleCollar e R := by
      simpa only [endDoubleTransition_source, mem_preimage] using hx
    have hyval : ((endDoubleTransition e hR x) : StandardCapSpace) ∈ endDoubleCollar e R := by
      rw [endDoubleTransition_apply_coe e hR hxval]
      exact endAxialReflection_maps_collar e hR hxval
    rw [heq x hxval, heq _ hyval]
    exact endDoubleTransition_metric e hR x hx u v



noncomputable def modifiedEndDoubleMetric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R)
    (hagrees : EqOn h.euclideanCoefficients g.euclideanCoefficients (endDoubleCollar e R)) :
    RiemannianMetric 3 (EndDouble e hR) := by
  let := endDoublePiece_nonempty e hR
  exact quotientMetric (fun _ : Bool => endTruncation e (R + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ R + 1 by linarith))
    (endDoubleOverlap e hR) (endDoubleOverlap_smooth e hR)
    (fun _ => modifiedEndDoublePieceMetric e h hR)
    (modifiedEndDoubleMetrics_compatible e h hR hagrees)



theorem modifiedEndDoubleMetric_preserves (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R)
    (hagrees : EqOn h.euclideanCoefficients g.euclideanCoefficients (endDoubleCollar e R))
    (i : Bool) :
    let := endDoublePieceChartedSpace e hR
    ∀ (x : EndDoublePiece e R) (u v : TangentSpace (𝓡 3) x),
      h.inner (x : StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) =
      (modifiedEndDoubleMetric e h hR hagrees).inner ((endDoubleOverlap e hR).include i x)
        (mfderiv (𝓡 3) (𝓡 3) ((endDoubleOverlap e hR).include i) x u)
        (mfderiv (𝓡 3) (𝓡 3) ((endDoubleOverlap e hR).include i) x v) := by
  let := endDoublePieceChartedSpace e hR
  let := endDoublePiece_nonempty e hR
  dsimp only
  intro x u v
  exact quotientMetric_preserves (fun _ : Bool => endTruncation e (R + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ R + 1 by linarith))
    (endDoubleOverlap e hR) (endDoubleOverlap_smooth e hR)
    (fun _ => modifiedEndDoublePieceMetric e h hR)
    (modifiedEndDoubleMetrics_compatible e h hR hagrees) i x u v




theorem modifiedEndDoubleParametrization_metric (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) {R : ℝ} (hR : 1 < R)
    (hagrees : EqOn h.euclideanCoefficients g.euclideanCoefficients (endDoubleCollar e R))
    (i : Bool) {x : StandardCapSpace} (hx : x ∈ endTruncation e (R + 1))
    (u v : TangentSpace (𝓡 3) x) :
    h.inner x u v =
      (modifiedEndDoubleMetric e h hR hagrees).inner (endDoubleParametrization e hR i x)
        (mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hR i) x u)
        (mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hR i) x v) := by
  let := endDoublePiece_nonempty e hR
  let := endDoublePieceChartedSpace e hR
  let := endDoublePiece_isManifold e hR
  let p : EndDoublePiece e R := ⟨x, hx⟩
  have hp := modifiedEndDoubleMetric_preserves e h hR hagrees i p u v
  rw [mfderiv_subtypeVal_singleton
    (endTruncation_isOpen e (show 0 ≤ R + 1 by linarith)) p] at hp
  change h.inner x u v = _ at hp
  rw [show x = (p : StandardCapSpace) from rfl,
    endDoubleParametrization_apply, endDoubleParametrization_mfderiv]
  exact hp




theorem modifiedEndDouble_curvatureDerivative_le (e : StandardCylindricalEnd g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    {R : ℝ} (hR : 1 < R)
    (hagrees : EqOn h.euclideanCoefficients g.euclideanCoefficients (endDoubleCollar e R))
    (m : ℕ) {C : ℝ} (hbound : ∀ x : StandardCapSpace, D.curvatureDerivativeNorm m x ≤ C)
    (D' : LeviCivitaData (modifiedEndDoubleMetric e h hR hagrees)) (q : EndDouble e hR) :
    D'.curvatureDerivativeNorm m q ≤ C := by
  obtain ⟨i, x, hx, rfl⟩ := endDoubleParametrization_cover e hR q
  rw [← D.curvatureDerivativeNorm_eq_pullback D'
    (endTruncation_isOpen e (show 0 ≤ R + 1 by linarith))
    (endDoubleParametrization_contMDiffOn e hR i)
    (fun _ hy => endDoubleParametrization_mfderiv_isInvertible e hR i hy)
    (fun _ hy u v => modifiedEndDoubleParametrization_metric e h hR hagrees i hy u v) m hx]
  exact hbound x

end PoincareConjecture.M34
