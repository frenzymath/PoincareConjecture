import PoincareConjecture.Proofs.M04.ConnectionScalar

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Function Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem mvfderiv_mlieBracket {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) f x (VectorField.mlieBracket (𝓡 n) X Y x) =
      mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (X x) -
        mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (X y)) x (Y x) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := extChartAt (𝓡 n) x
  let p := e x
  let F := f ∘ e.symm
  let P := VectorField.mpullbackWithin 𝓘(ℝ, E) (𝓡 n) e.symm X (Set.range (𝓡 n))
  let Q := VectorField.mpullbackWithin 𝓘(ℝ, E) (𝓡 n) e.symm Y (Set.range (𝓡 n))
  have he : e.symm p = x := extChartAt_to_inv x
  have hec {q : E} (hq : q ∈ e.target) :
      ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ e.symm q := by
    simpa +instances only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := ∞) x hq)
  have hp : p ∈ e.target := mem_extChartAt_target x
  have htwo : (2 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞) htwo
  have hfa := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hXa := (hX x hx).contMDiffAt (hU.mem_nhds hx)
  have hYa := (hY x hx).contMDiffAt (hU.mem_nhds hx)
  have hP : DifferentiableAt ℝ P p := by
    have h := (hXa.mdifferentiableAt (by simp)).mdifferentiableWithinAt (s := Set.univ)
    simpa +instances only [P, p, e, E, ModelWithCorners.range_eq_univ, Set.preimage_univ,
      Set.univ_inter, differentiableWithinAt_univ] using!
      h.differentiableWithinAt_mpullbackWithin_vectorField
  have hQ : DifferentiableAt ℝ Q p := by
    have h := (hYa.mdifferentiableAt (by simp)).mdifferentiableWithinAt (s := Set.univ)
    simpa +instances only [Q, p, e, E, ModelWithCorners.range_eq_univ, Set.preimage_univ,
      Set.univ_inter, differentiableWithinAt_univ] using!
      h.differentiableWithinAt_mpullbackWithin_vectorField
  have hF : ContDiffAt ℝ ∞ F p := by
    have hfa' : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e.symm p) := by
      simpa +instances only [he] using hfa
    exact (hfa'.comp p (hec hp)).contDiffAt
  have hid : mfderiv 𝓘(ℝ, E) (𝓡 n) e.symm p = ContinuousLinearMap.id ℝ E := by
    simpa +instances only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hcomp (a : M → ℝ) (ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x) :
      fderiv ℝ (a ∘ e.symm) p = mvfderiv (𝓡 n) a x := by
    have ha' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a (e.symm p) := by
      simpa +instances only [he] using ha
    erw [← mfderiv_eq_fderiv, mfderiv_comp p ha' ((hec hp).mdifferentiableAt (by simp)),
      hid, ContinuousLinearMap.comp_id]
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) a (e.symm p) = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) a x
    erw [he]
  have hpT : e.target ∈ 𝓝 p := by
    simpa +instances only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] using
      (extChartAt_target_mem_nhdsWithin (I := 𝓡 n) x)
  have hpU : e.symm ⁻¹' U ∈ 𝓝 p := by
    apply (hec hp).continuousAt.preimage_mem_nhds
    simpa +instances only [he] using hU.mem_nhds hx
  have hD (W : (y : M) → TangentSpace (𝓡 n) y) :
      (fun q ↦ fderiv ℝ F q
        (VectorField.mpullbackWithin 𝓘(ℝ, E) (𝓡 n) e.symm W (Set.range (𝓡 n)) q))
      =ᶠ[𝓝 p] (fun q ↦ mvfderiv (𝓡 n) f (e.symm q) (W (e.symm q))) := by
    filter_upwards [hpT, hpU] with q hqT hqU
    have hfq := ((hf (e.symm q) hqU).contMDiffAt (hU.mem_nhds hqU)).mdifferentiableAt (by simp)
    have hiq := (hec hqT).mdifferentiableAt (by simp)
    have hInv : (mfderiv 𝓘(ℝ, E) (𝓡 n) e.symm q).IsInvertible := by
      simpa +instances only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hqT)
    erw [← mfderiv_eq_fderiv, mfderiv_comp q hfq hiq]
    simp +instances only [VectorField.mpullbackWithin_apply,
      ModelWithCorners.range_eq_univ, mfderivWithin_univ]
    change mvfderiv (𝓡 n) f (e.symm q)
        ((mfderiv 𝓘(ℝ, E) (𝓡 n) e.symm q)
          ((mfderiv 𝓘(ℝ, E) (𝓡 n) e.symm q).inverse (W (e.symm q)))) =
      mvfderiv (𝓡 n) f (e.symm q) (W (e.symm q))
    exact congrArg (mvfderiv (𝓡 n) f (e.symm q)) (hInv.self_apply_inverse _)
  have hPx : P p = X x := by
    change (mfderivWithin 𝓘(ℝ, E) (𝓡 n) e.symm (Set.range (𝓡 n)) p).inverse
      (X (e.symm p)) = X x
    have hXe : (X (e.symm p) : E) = X x := congrArg (fun y : M ↦ (X y : E)) he
    erw [hXe]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := 𝓡 n) (x := x) (X x)
  have hQx : Q p = Y x := by
    change (mfderivWithin 𝓘(ℝ, E) (𝓡 n) e.symm (Set.range (𝓡 n)) p).inverse
      (Y (e.symm p)) = Y x
    have hYe : (Y (e.symm p) : E) = Y x := congrArg (fun y : M ↦ (Y y : E)) he
    erw [hYe]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := 𝓡 n) (x := x) (Y x)
  have hbr : VectorField.mlieBracket (𝓡 n) X Y x = VectorField.lieBracket ℝ P Q p := by
    simp +instances only [P, Q, p, e, E, VectorField.mlieBracket,
      VectorField.mlieBracketWithin_apply,
      Set.preimage_univ, Set.univ_inter, ModelWithCorners.range_eq_univ,
      VectorField.lieBracketWithin_univ, mfderiv_extChartAt_self,
      ContinuousLinearMap.inverse_id]
    rfl
  have hmin : (minSmoothness ℝ 2 : ℕ∞ω) ≤ ∞ := by
    simpa +instances only [minSmoothness_of_isRCLikeNormedField] using htwo
  have h := VectorField.fderiv_apply_lieBracket hF hmin hQ hP
  erw [(hD Y).fderiv_eq, (hD X).fderiv_eq] at h
  have hYf := (contMDiffOn_directional_derivative hU hf hY).contMDiffAt (hU.mem_nhds hx)
  have hXf := (contMDiffOn_directional_derivative hU hf hX).contMDiffAt (hU.mem_nhds hx)
  erw [hcomp f (hfa.mdifferentiableAt (by simp)),
    hcomp _ (hYf.mdifferentiableAt (by simp)), hcomp _ (hXf.mdifferentiableAt (by simp)),
    hPx, hQx, ← hbr] at h
  exact h

end PoincareConjecture.M04
