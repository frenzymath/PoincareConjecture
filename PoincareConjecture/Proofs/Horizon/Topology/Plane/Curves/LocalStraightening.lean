import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

theorem exists_local_straightening
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} {t : ℝ}
    (hf : ContDiffAt ℝ ∞ f t) (hregular : deriv f t ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin 2),
      w ≠ 0 ∧ inner ℝ (deriv f t) w = 0 ∧
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
        (t, 0) ∈ F.source ∧
        (∀ q : ℝ × ℝ, F q = f q.1 + q.2 • w) ∧
        ContDiffAt ℝ ∞ F (t, 0) ∧ ContDiffAt ℝ ∞ F.symm (f t) := by
  let E := Complex.orthonormalBasisOneI.repr
  let z : ℂ := E.symm (deriv f t)
  have hz : z ≠ 0 := by
    intro h
    apply hregular
    have := congrArg E h
    simpa [z] using this
  let w := E (Complex.I * z)
  have hw : w ≠ 0 := by
    intro h
    apply mul_ne_zero Complex.I_ne_zero hz
    exact E.injective (by simpa [w] using h)
  have hzmap : E z = deriv f t := E.apply_symm_apply _
  have horthogonal : inner ℝ (deriv f t) w = 0 := by
    rw [← hzmap]
    change inner ℝ (E z) (E (Complex.I * z)) = 0
    rw [E.inner_map_map]
    exact real_inner_I_smul_self ℂ z
  let L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (Complex.equivRealProdCLM.symm.trans
      (ContinuousLinearEquiv.smulLeft (Units.mk0 z hz))).trans E.toContinuousLinearEquiv
  have hL (q : ℝ × ℝ) : L q = q.1 • deriv f t + q.2 • w := by
    change E (z * Complex.equivRealProdCLM.symm q) = _
    have hmul : z * Complex.equivRealProdCLM.symm q =
        q.1 • z + q.2 • (Complex.I * z) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp only [Complex.real_smul]
      ring
    rw [hmul, map_add, map_smul, map_smul, hzmap]
  let G : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun q => f q.1 + q.2 • w
  have hG : ContDiffAt ℝ ∞ G (t, 0) :=
    (hf.comp (t, 0) contDiffAt_fst).add (contDiffAt_snd.smul contDiffAt_const)
  have hdG : HasStrictFDerivAt G (L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (t, 0) := by
    convert! ((hf.hasStrictDerivAt (by simp)).hasStrictFDerivAt.comp (t, 0)
      hasStrictFDerivAt_fst).add
      ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (t, (0 : ℝ)))).smul_const w) using 1
    exact ContinuousLinearMap.ext hL
  let F := hdG.toOpenPartialHomeomorph G
  have hsource : (t, 0) ∈ F.source := hdG.mem_toOpenPartialHomeomorph_source
  have hbase : F (t, 0) = f t := by simp [F, G]
  have hinverse : F.symm (f t) = (t, 0) := by
    rw [← hbase]
    exact F.left_inv hsource
  refine ⟨w, hw, horthogonal, F, hsource, fun _ => rfl, hG, ?_⟩
  apply F.contDiffAt_symm (hbase ▸ F.map_source hsource)
  · rw [hinverse]
    exact hdG.hasFDerivAt
  · rw [hinverse]
    exact hG

end Poincare.Topology.Plane.Curves
