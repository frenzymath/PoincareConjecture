import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Finite coordinate reconstruction of continuous bilinear maps

Two coordinate basis expansions reconstruct a continuous bilinear map as
a finite sum of rank-one input covectors with its vector-valued basis
evaluations. This includes either empty coordinate index and is used for
Morgan-Tian Section 12.5, pp. 309-319.
-/

set_option autoImplicit false

open scoped BigOperators

/-- A continuous bilinear map on finite `PiLp` spaces is the sum of its
coordinate evaluations, with the first and second input orders retained
(Section 12.5, pp. 309-319). -/
theorem ContinuousLinearMap.eq_sum_piLp_bilinear_coordinates
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {𝕜 I J F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : (PiLp p fun _ : I => 𝕜) →L[𝕜] (PiLp q fun _ : J => 𝕜) →L[𝕜] F) :
    L = ∑ i : I, ∑ j : J,
      (PiLp.proj p (fun _ : I => 𝕜) i).smulRight
        ((PiLp.proj q (fun _ : J => 𝕜) j).smulRight
          (L (PiLp.single p i 1) (PiLp.single q j 1))) := by
  let e : I → PiLp p (fun _ : I => 𝕜) := fun i => PiLp.single p i 1
  let f : J → PiLp q (fun _ : J => 𝕜) := fun j => PiLp.single q j 1
  have hu (u : PiLp p fun _ : I => 𝕜) : u = ∑ i : I, u i • e i := by
    simpa [e, PiLp.basisFun_repr, PiLp.basisFun_apply] using
      ((PiLp.basisFun p 𝕜 I).sum_repr u).symm
  have hv (v : PiLp q fun _ : J => 𝕜) : v = ∑ j : J, v j • f j := by
    simpa [f, PiLp.basisFun_repr, PiLp.basisFun_apply] using
      ((PiLp.basisFun q 𝕜 J).sum_repr v).symm
  ext u v
  conv_lhs => rw [hu u, hv v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change v j • (u i • L (e i) (f j)) = u i • (v j • L (e i) (f j))
  exact smul_comm _ _ _

/-- The finite coordinate reconstruction of a bilinear map is itself a
continuous linear map in its vector-valued coefficients
(Section 12.5, pp. 309-319). -/
noncomputable def ContinuousLinearMap.piLpBilinearFromCoordinates
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {𝕜 I J F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [Fintype J] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] :
    (I → J → F) →L[𝕜]
      (PiLp p fun _ : I => 𝕜) →L[𝕜] (PiLp q fun _ : J => 𝕜) →L[𝕜] F :=
  ∑ i : I, ∑ j : J,
    ((ContinuousLinearMap.smulRightL 𝕜 (PiLp p fun _ : I => 𝕜)
      ((PiLp q fun _ : J => 𝕜) →L[𝕜] F) (PiLp.proj p (fun _ : I => 𝕜) i)).comp
      (ContinuousLinearMap.smulRightL 𝕜 (PiLp q fun _ : J => 𝕜) F
        (PiLp.proj q (fun _ : J => 𝕜) j))).comp
      ((ContinuousLinearMap.proj j : (J → F) →L[𝕜] F).comp
        (ContinuousLinearMap.proj i : (I → J → F) →L[𝕜] (J → F)))

/-- The continuous reconstruction map evaluates to its finite rank-one
coordinate sum (Section 12.5, pp. 309-319). -/
theorem ContinuousLinearMap.piLpBilinearFromCoordinates_apply
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {𝕜 I J F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [Fintype J] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (a : I → J → F) :
    ContinuousLinearMap.piLpBilinearFromCoordinates (p := p) (q := q) (𝕜 := 𝕜) a =
      ∑ i : I, ∑ j : J, (PiLp.proj p (fun _ : I => 𝕜) i).smulRight
        ((PiLp.proj q (fun _ : J => 𝕜) j).smulRight (a i j)) := by
  simp only [ContinuousLinearMap.piLpBilinearFromCoordinates, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl

/-- Reconstructing the coordinate evaluations returns the original
continuous bilinear map (Section 12.5, pp. 309-319). -/
theorem ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations
    {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {𝕜 I J F : Type*} [NontriviallyNormedField 𝕜]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (L : (PiLp p fun _ : I => 𝕜) →L[𝕜] (PiLp q fun _ : J => 𝕜) →L[𝕜] F) :
    ContinuousLinearMap.piLpBilinearFromCoordinates
      (fun i j => L (PiLp.single p i 1) (PiLp.single q j 1)) = L := by
  rw [ContinuousLinearMap.piLpBilinearFromCoordinates_apply]
  exact L.eq_sum_piLp_bilinear_coordinates.symm
