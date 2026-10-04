import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Neck.NeckJetNonnegative
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/RoundCylinderGram.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Positivity of the literal round-cylinder Gram matrix

The model in Morgan-Tian Definition 2.18, p. 31, is the line times
the unit sphere with metric multiplied by two. Its frozen evolving
extension is positive for `u < 1`. The coordinate computation below
uses the actual sphere inclusion and inverse-chart differentials.
-/

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

namespace PoincareMT.SurgeryVolume

/-- The three displayed cylinder coordinate vectors are independent
(the product coordinates of MT Definition 2.18, p. 31). -/
theorem roundCylinderCoordinateBasis_linearIndependent :
    LinearIndependent ℝ roundCylinderCoordinateBasis := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  fin_cases i
  · simpa [Fin.sum_univ_three, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun_apply] using
      congrArg (fun x : RoundCylinderCoordinates => x.1 0) ha
  · simpa [Fin.sum_univ_three, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun_apply] using
      congrArg (fun x : RoundCylinderCoordinates => x.1 1) ha
  · simpa [Fin.sum_univ_three, roundCylinderCoordinateBasis] using
      congrArg (fun x : RoundCylinderCoordinates => x.2) ha

/-- The actual evolving-cylinder Gram matrix is positive in every sphere
chart for `u < 1` (MT Definitions 2.16 and 2.18, pp. 30-31). -/
theorem roundCylinderGram_posDef (u : ℝ) (hu : u < 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates)
    (hp : p.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).PosDef := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hc : c.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(contMDiffOn_chart (I := 𝓡 2) (n := 1)).mdifferentiableOn one_ne_zero,
      (contMDiffOn_chart_symm (I := 𝓡 2) (n := 1)).mdifferentiableOn one_ne_zero⟩
  have hi : Function.Injective
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1) := hc.symm.mfderiv_injective hp
  have hs : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun x : UnitTwoSphere => x.1) (c.symm p.1)) := by
    convert! injective_mvfderiv_subtypeVal_sphere (c.symm p.1)
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) (c.symm p.1)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1)
  have hD : Function.Injective D := hs.comp hi
  let s := Real.sqrt (2 * (1 - u))
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  let L : RoundCylinderCoordinates →ₗ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin 3) × ℝ) :=
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 3) × ℝ)).symm.toLinearMap.comp
      ((s • D.toLinearMap).prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have hL : Function.Injective L := by
    intro a b hab
    apply Prod.ext
    · apply hD
      apply (smul_right_inj hspos.ne').mp
      exact congrArg (fun x : WithLp 2 (EuclideanSpace ℝ (Fin 3) × ℝ) =>
        (WithLp.ofLp x).1) hab
    · have h := congrArg (fun x : WithLp 2 (EuclideanSpace ℝ (Fin 3) × ℝ) =>
        (WithLp.ofLp x).2) hab
      exact h
  have hli := roundCylinderCoordinateBasis_linearIndependent.map' L
    (LinearMap.ker_eq_bot.mpr hL)
  have hgram : roundCylinderGram u c p =
      Matrix.gram ℝ (fun i => L (roundCylinderCoordinateBasis i)) := by
    ext i j
    simp only [Matrix.gram_apply, WithLp.prod_inner_apply]
    change 2 * (1 - u) * inner ℝ (D (roundCylinderCoordinateBasis i).1)
        (D (roundCylinderCoordinateBasis j).1) +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 =
      inner ℝ (s • D (roundCylinderCoordinateBasis i).1)
        (s • D (roundCylinderCoordinateBasis j).1) +
        inner ℝ (roundCylinderCoordinateBasis i).2 (roundCylinderCoordinateBasis j).2
    rw [real_inner_smul_left, real_inner_smul_right, Real.inner_apply]
    have hs2 : s * s = 2 * (1 - u) := Real.mul_self_sqrt (by linarith)
    simp only [← mul_assoc, hs2]
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- For the actual positive cylinder model, the zeroth error term is
bounded by the complete jet sum (MT Definition 2.16, p. 30). -/
theorem roundCylinder_zeroth_le_jetErrorSquared_of_lt_one (u : ℝ) (hu : u < 1)
    (B : RoundCylinderTwoTensor) (k : ℕ) (z : RoundCylinderSpace) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
        ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)
        (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) z.1)
          B 0 ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2)) ≤
      roundCylinderJetErrorSquared u B k z := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  have hp : p.1 ∈ c.target := c.map_source (mem_chart_source _ _)
  have hG : (roundCylinderGram u c p).PosDef := roundCylinderGram_posDef u hu z.1 p hp
  exact roundCylinder_zeroth_le_jetErrorSquared u B k z hG.inv.posSemidef

end PoincareMT.SurgeryVolume
