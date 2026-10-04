import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckCylinderOrdinary

/-!
# The exact based metric on the original open source

Lemma 17.2, MT pp. 397-398. The based identity is equality of the
whole dependent slice map. Its metric pullback therefore identifies
both tangent slots of the actual ordinary terminal metric.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Proofs.M47

/-- The actual ordinary metric at the based terminal time is the
literal pullback by inclusion of the unchanged open source. -/
theorem neck_ordinary_terminal_metric
    {F : SurgeryFlowData.{u}} {T : ℝ} {I J : Set ℝ}
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 I U) (hzero : (0 : ℝ) ∈ I)
    (hbased : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (G : RicciFlow 3 U J)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      (F.metric (T + 0 / 1)).inner (e.forward 0 hzero x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward 0 hzero y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward 0 hzero y.val) x w) =
          (G.metric (T + 0 / 1)).inner x v w)
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    (G.metric T).inner x v w = (F.metric T).inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) := by
  have hfunctions :
      (⟨T + 0 / 1, fun y : U => e.forward 0 hzero y.val⟩ :
        (t : ℝ) × (U → (F.slice t).carrier)) =
          ⟨T, (Subtype.val : U → (F.slice T).carrier)⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact hbased _ y.val y.property
  have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
    (F.metric p.1).inner (p.2 x)
      (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
  exact (congrArg (fun t => (G.metric t).inner x v w)
    (show T + 0 / 1 = T by simp only [zero_div, add_zero])).symm.trans
      ((hmetric x v w).symm.trans hpull)

end PoincareMT.Proofs.M47
