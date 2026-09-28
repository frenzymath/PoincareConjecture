import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleManifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Construction

set_option autoImplicit false

open Set Topology Filter Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endDoublePieceMetric (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    let := endDoublePiece_isManifold e hL
    RiemannianMetric 3 (EndDoublePiece e L) := by
  let := endDoublePieceChartedSpace e hL
  let := endDoublePiece_isManifold e hL
  exact g.pullbackOfLocalDiffeomorph Subtype.val
    (endDoublePiece_subtypeVal_isLocalDiffeomorph e hL)

theorem endDoublePieceMetric_inner (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    let := endDoublePiece_isManifold e hL
    ∀ (x : EndDoublePiece e L) (u v : TangentSpace (𝓡 3) x),
      (endDoublePieceMetric e hL).inner x u v = g.inner (x : StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) := by
  dsimp only
  intro x u v
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem endDoubleTransition_mfderiv_subtypeVal (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    ∀ (x : EndDoublePiece e L) (_hx : x ∈ (endDoubleTransition e hL).source)
      (u : TangentSpace (𝓡 3) x),
      mfderiv (𝓡 3) (𝓡 3) Subtype.val (endDoubleTransition e hL x)
        (mfderiv (𝓡 3) (𝓡 3) (endDoubleTransition e hL) x u) =
      mfderiv (𝓡 3) (𝓡 3) (endAxialReflection e (2 * L)) (x : StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u) := by
  let := endDoublePieceChartedSpace e hL
  dsimp only
  intro x hx u
  have hxval : (x : StandardCapSpace) ∈ endDoubleCollar e L := by
    simpa only [endDoubleTransition_source, mem_preimage] using hx
  have heq : ((Subtype.val : EndDoublePiece e L → StandardCapSpace) ∘
      endDoubleTransition e hL) =ᶠ[𝓝 x]
      endAxialReflection e (2 * L) ∘ Subtype.val := by
    filter_upwards [(endDoubleTransition e hL).open_source.mem_nhds hx] with y hy
    exact endDoubleTransition_apply_coe e hL
      (by simpa only [endDoubleTransition_source, mem_preimage] using hy)
  have hi := (endDoublePiece_subtypeVal_isLocalDiffeomorph e hL).mdifferentiable (by simp)
  have hr := ((endDoubleTransition_contMDiffOn e hL).contMDiffAt
    ((endDoubleTransition e hL).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have ha := ((endAxialReflection_collar_contMDiffOn e hL).contMDiffAt
    ((endDoubleCollar_isOpen e hL).mem_nhds hxval)).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x (hi _) hr, mfderiv_comp x ha (hi x)] at hd
  exact congrArg (fun A : StandardCapSpace →L[ℝ] StandardCapSpace => A u) hd

set_option backward.isDefEq.respectTransparency false in

theorem endDoubleTransition_metric (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    let := endDoublePiece_isManifold e hL
    ∀ (x : EndDoublePiece e L) (_hx : x ∈ (endDoubleTransition e hL).source)
      (u v : TangentSpace (𝓡 3) x),
      (endDoublePieceMetric e hL).inner x u v =
      (endDoublePieceMetric e hL).inner (endDoubleTransition e hL x)
        (mfderiv (𝓡 3) (𝓡 3) (endDoubleTransition e hL) x u)
        (mfderiv (𝓡 3) (𝓡 3) (endDoubleTransition e hL) x v) := by
  let := endDoublePieceChartedSpace e hL
  let := endDoublePiece_isManifold e hL
  dsimp only
  intro x hx u v
  have hxval : (x : StandardCapSpace) ∈ endDoubleCollar e L := by
    simpa only [endDoubleTransition_source, mem_preimage] using hx
  rw [endDoublePieceMetric_inner, endDoublePieceMetric_inner,
    endDoubleTransition_mfderiv_subtypeVal e hL x hx,
    endDoubleTransition_mfderiv_subtypeVal e hL x hx,
    endDoubleTransition_apply_coe e hL hxval]
  obtain ⟨z, hz, hxz⟩ := hxval
  have hlow : L - 1 < z.2 := hz.2.1
  have hupp : z.2 < L + 1 := hz.2.2
  rw [← hxz]
  exact endAxialReflection_metric e (2 * L) (by linarith) (by linarith) _ _

theorem endDoubleMetrics_compatible (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePiece_nonempty e hL
    CompatibleMetrics (fun _ : Bool => endTruncation e (L + 1))
      (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
      (endDoubleOverlap e hL) (fun _ => endDoublePieceMetric e hL) := by
  let := endDoublePiece_nonempty e hL
  let := endDoublePieceChartedSpace e hL
  let := endDoublePiece_isManifold e hL
  dsimp only [CompatibleMetrics]
  intro i j x hx u v
  by_cases hij : i = j
  · subst j
    rw [(endDoubleOverlap e hL).self]
    change (endDoublePieceMetric e hL).inner x u v =
      (endDoublePieceMetric e hL).inner x
        (mfderiv (𝓡 3) (𝓡 3) id x u) (mfderiv (𝓡 3) (𝓡 3) id x v)
    rw [mfderiv_id]
    rfl
  · have ht : (endDoubleOverlap e hL).transition i j = endDoubleTransition e hL :=
      twoPieceOverlap_transition_ne _ _ hij
    rw [ht] at hx ⊢
    exact endDoubleTransition_metric e hL x hx u v

noncomputable def endDoubleMetric (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : RiemannianMetric 3 (EndDouble e hL) := by
  let := endDoublePiece_nonempty e hL
  exact quotientMetric (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL)
    (fun _ => endDoublePieceMetric e hL) (endDoubleMetrics_compatible e hL)

theorem endDoubleMetric_preserves (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) :
    let := endDoublePieceChartedSpace e hL
    ∀ (x : EndDoublePiece e L) (u v : TangentSpace (𝓡 3) x),
      g.inner (x : StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x u)
        (mfderiv (𝓡 3) (𝓡 3) Subtype.val x v) =
      (endDoubleMetric e hL).inner ((endDoubleOverlap e hL).include i x)
        (mfderiv (𝓡 3) (𝓡 3) ((endDoubleOverlap e hL).include i) x u)
        (mfderiv (𝓡 3) (𝓡 3) ((endDoubleOverlap e hL).include i) x v) := by
  let := endDoublePieceChartedSpace e hL
  let := endDoublePiece_nonempty e hL
  dsimp only
  intro x u v
  exact quotientMetric_preserves (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL)
    (fun _ => endDoublePieceMetric e hL) (endDoubleMetrics_compatible e hL) i x u v

end PoincareConjecture.M34
