import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Local.ConeWeakFilling
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.PhaseTargetAngle

/-! The actual continuous disk competitor has a real original-circle
phase with its prescribed continuous boundary lift. The lift is produced
by the covering theorem on the plane, and boundary uniqueness fixes it.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- Construct a genuine continuous real circle phase for a cone disk with the prescribed
boundary lift. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_cone_real_phase
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {e : Q.charts.Point → EuclideanSpace ℝ (Fin m)} {gamma : ℝ → Q.charts.Point}
    (A : M64ObservedConeDisk (n := (n + 1) + 1) e gamma)
    {L : ℝ → ℝ} (hL : Continuous L)
    (hquot : ∀ x, P.circle.quotient (L x) = (gamma x).1.2) :
    ∃ u : LoopPlane → ℝ, Continuous u ∧
      (∀ p, P.circle.quotient (u p) = (A.map p).1.2) ∧
      ∀ x, u (angularPoint x) = L x := by
  let f : LoopPlane → P.circle.Point := fun p => (A.map p).1.2
  have hf : Continuous f := continuous_snd.comp (continuous_fst.comp A.continuous)
  have hbase : P.circle.quotient (L 0) = f (angularPoint 0) := by
    dsimp only [f]
    rw [A.boundary]
    exact hquot 0
  let cov := AddCircle.isCoveringMap_coe circumference
  obtain ⟨u, hu, -⟩ := cov.existsUnique_continuousMap_lifts
    ⟨f, hf⟩ (angularPoint 0) (L 0) hbase
  have huq (p : LoopPlane) : P.circle.quotient (u p) = (A.map p).1.2 := congrFun hu.2 p
  have hc : Continuous (angularPoint : ℝ → LoopPlane) := by unfold angularPoint; fun_prop
  have heq := cov.eq_of_comp_eq (u.continuous.comp hc) hL
    (show (fun x => (u (angularPoint x) : AddCircle circumference)) =
      (fun x => (L x : AddCircle circumference)) from by
        funext x
        exact (huq _).trans ((congrArg (fun q : Q.charts.Point => q.1.2)
          (A.boundary x)).trans (hquot x).symm)) 0 hu.1
  exact ⟨u, u.continuous, huq, congrFun heq⟩

end PoincareMT.M64
