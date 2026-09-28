import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarHalfSpaceGradient












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => BoundaryTangential.halfSpace 2






theorem m64Vector_halfSpace_H3_continuous_gradient
    {m : ℕ} {u : Plane → EuclideanSpace ℝ (Fin m)}
    (hc : HasCompactSupport u)
    (hu : ∀ b : Fin m, Euclidean.MemWkp 3 2 (fun x => u x b) Half) :
    ∃ G : Fin 2 → Plane → EuclideanSpace ℝ (Fin m),
      (∀ i, Continuous (G i)) ∧
      ∀ i b, chosenWeakPartial' 2 i (fun x => u x b) Half =ᵐ[
        volume.restrict Half] (fun x => G i x b) := by
  have hcoord (b : Fin m) : HasCompactSupport (fun x => u x b) := by
    have hcomp := hc.comp_left (EuclideanSpace.proj (𝕜 := ℝ) b).map_zero
    change HasCompactSupport ((EuclideanSpace.proj (𝕜 := ℝ) b) ∘ u)
    exact hcomp
  choose G hGc hG using fun b : Fin m =>
    M64Uniformization.scalar_halfSpace_H3_continuous_gradient (hcoord b) (hu b)
  let V : Fin 2 → Plane → EuclideanSpace ℝ (Fin m) := fun i x =>
    WithLp.toLp 2 (fun b => G b i x)
  have hVc (i : Fin 2) : Continuous (V i) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
    apply continuous_pi
    intro b
    exact (hGc b i).comp continuous_id
  refine ⟨V, hVc, ?_⟩
  intro i b
  simpa only [V] using hG b i

end PoincareConjecture
