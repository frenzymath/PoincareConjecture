import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.RicciFlowAnalysis
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Local.HessianTrace
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.RegularSmooth
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Normal

/-!
# The symmetric bilinear raw reduced-length Hessian

Actual smoothness on the open joint image supplies the ordinary
slice Hessian and its symmetry. Pulling both arguments through the
specified slice tangent equivalence retains the frozen horizontal
pairing. Morgan-Tian Lemma 6.40, Proposition 6.43 and Claim 6.44,
pp. 126-128.
-/

set_option autoImplicit false
-- The algebraic tangent fibers keep their ambient model coordinates.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The raw reduced-length Hessian at an actual regular slice point
is a symmetric bilinear form on the specified horizontal fiber,
Lemma 6.40, Proposition 6.43 and Claim 6.44, pp. 126-128. -/
theorem reducedLengthHessianPairing_exists_symm_bilinear
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {τ : ℝ} (q : (G.slices (T - τ)).Point)
    (hq : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :
    ∃ B : LinearMap.BilinForm ℝ (G.Horizontal q.val),
      (∀ v w, M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x) v w =
        B v w) ∧ ∀ v w, B v w = B w v := by
  let S := G.slices (T - τ)
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) S.Point := S.chartedSpace
  let D := G.leafwise.sliceConnection (T - τ)
  let f : S.Point → ℝ := fun r => M14ReducedLengthAt G T 0 x r.val
  let j := S.tangentEquiv q
  obtain ⟨H, hH⟩ := hessian_exists_bilinear D f q
    (reducedLengthAt_slice_contMDiffAt hM04 hM12 E q hq)
  let A : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) q) := {
    toFun := fun v => (H v).toLinearMap
    map_add' := by
      intro v w
      ext z
      exact congrArg (fun C : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => C z) (H.map_add v w)
    map_smul' := by
      intro c v
      ext z
      exact congrArg (fun C : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => C z) (H.map_smul c v) }
  let B := A.comp j.symm.toLinearMap j.symm.toLinearMap
  have hpair (v w : G.Horizontal q.val) :
      M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x) v w = B v w :=
    hH (j.symm v) (j.symm w)
  refine ⟨B, hpair, ?_⟩
  let O := range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  let U := (fun r : S.Point => r.val) ⁻¹' O
  have hU : IsOpen U := (jointMap_range_isOpen E).preimage S.inclusion_smooth.continuous
  have hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f U :=
    (reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E).comp
      S.inclusion_smooth.contMDiffOn (fun _ hr => hr)
  intro v w
  rw [← hpair, ← hpair]
  exact M04.hessian_symm_on D hU hf hq (j.symm v) (j.symm w)

end PoincareMT.M14
