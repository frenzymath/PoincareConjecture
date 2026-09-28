import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.ClosedStripDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSliceDifferential

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

omit [IsManifold (𝓡 n) ∞ M] in

theorem closedStrip_horizontal_velocity {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (x : ℝ) :
    curveVelocity (fun y => f (annulusPoint y s)) x =
      mfderivWithin (𝓡 2) (𝓡 n) f S (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) := by
  have hline := m64AnnulusPoint_horizontal_hasDerivAt s x
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun y => annulusPoint y s) x := hline.differentiableAt.mdifferentiableAt
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun y => annulusPoint y s) x 1 =
      EuclideanSpace.single (0 : Fin 2) 1 := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hchain := mfderivWithin_comp x
    ((hf (annulusPoint x s) hs).mdifferentiableWithinAt one_ne_zero)
    (s := univ) (u := S) hmd.mdifferentiableWithinAt (fun _ _ => hs)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, ℝ) (x := x))
  simp only [mfderivWithin_univ] at hchain
  have h := congrArg (fun L => L (1 : ℝ)) hchain
  simpa +instances only [curveVelocity, Function.comp_def,
    ContinuousLinearMap.comp_apply, hd] using! h

theorem annulus_closedStrip_slice_immersed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ x, curveVelocity (n := n) (fun y => A.map (annulusPoint y s)) x ≠ 0 := by
  have hstrip := annulus_strip_within_injective A hf hinj
  intro x hzero
  rw [closedStrip_horizontal_velocity hf hs x] at hzero
  have heq := hstrip (annulusPoint x s) hs
    (hzero.trans (map_zero (mfderivWithin (𝓡 2) (𝓡 n) A.map S (annulusPoint x s))).symm)
  have hcoord := congrArg (fun p : LoopPlane => p 0) heq
  change (1 : ℝ) = 0 at hcoord
  exact one_ne_zero hcoord

end PoincareConjecture.M64.RampTransport
