import PoincareConjecture.Statements.Ch06.LGeometry
import PoincareConjecture.Proofs.M09.ExponentialAction
import PoincareConjecture.Proofs.M09.FamilyEulerEquation
import PoincareConjecture.Proofs.M09.InitialVariationBoundary









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_action_initial_differential
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∀ W : TangentSpace (𝓡 n) p,
      fderiv ℝ (fun V ↦ A.action V b) Z W =
        2 * Real.sqrt b * (F.metric (T - b)).inner (A.gamma Z b)
          (curveVelocity (n := n) (A.gamma Z) b) (A.sliceDifferential Z b W) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  intro W
  let E := TangentSpace (𝓡 n) p
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  obtain ⟨D, hfirst⟩ := hL.first_variation 0 b le_rfl hb hmax.le (A.path Z b hb hmax) V
  have hresidual := lExponentialFamily_firstVariationResidualIntegral_eq_zero
    hM04 hτmax hwindow A Z b hb hmax V D
  have hboundary := initialVectorVariation_boundaryTerm A Z W b hb hmax
  rw [hresidual, add_zero, hboundary] at hfirst
  have haction := lExponentialFamily_action_contDiffOn hM04 hτmax hwindow A
  have hpoint := haction.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show (Z, b) ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, hb, hmax⟩))
  have hi : ContDiffAt ℝ ∞ (fun Y : E ↦ (Y, b)) Z :=
    contDiffAt_id.prodMk contDiffAt_const
  have hslice := hpoint.comp Z hi
  have hfd := (hslice.differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun u : ℝ ↦ Z + u • W) W 0 := by
    have hsmul : HasDerivAt (fun u : ℝ ↦ u • W) W 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const W
    exact hsmul.const_add Z
  have hreal := hfd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hvar : variationLLength V = fun u : ℝ ↦ A.action (Z + u • W) b :=
    funext fun u ↦ initialVectorVariation_action A Z W b hb hmax u
  rw [hvar] at hfirst
  exact hreal.unique hfirst

end PoincareConjecture.Proofs.M09
