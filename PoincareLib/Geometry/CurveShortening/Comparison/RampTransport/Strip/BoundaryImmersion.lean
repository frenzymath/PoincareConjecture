import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Closed.StripDifferential
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Annulus.SliceDifferential

/-!
# Actual horizontal immersion on the closed covering strip

The within chain rule identifies literal boundary velocities with the
horizontal column of the minimum's injective within differential.
Source: MT2007 Lemmas 19.15 and 19.31, pp. 447-449 and 464-466; ramp
transport trimming derivation, literal C1 boundary labels.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

omit [IsManifold (𝓡 n) ∞ M] in
/-- The actual velocity of every closed-strip horizontal slice is the horizontal column of
its within differential, including the two boundary slices. Source: Morgan--Tian Lemma
19.31, printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
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

/-- Injectivity of the actual closed-annulus within differential makes every horizontal
slice of its closed periodic strip immersed. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
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

end PoincareMT.M64.RampTransport
