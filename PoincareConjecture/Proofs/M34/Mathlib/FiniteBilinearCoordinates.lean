import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false

open scoped BigOperators

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
