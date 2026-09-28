import PoincareConjecture.Proofs.M08.VariationAcceleration
import PoincareConjecture.Proofs.M08.GlobalCurveExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def affineParametricExtension {C : Set ℝ} {α : ℝ → M}
    {Y Z : ∀ s, TangentSpace (𝓡 n) (α s)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EZ : ParametricAlongCurveExtensionOn C α Z) (c : ℝ) :
    ParametricAlongCurveExtensionOn C α (fun s ↦ Y s + c • Z s) where
  extension r x := EY.extension r x + c • EZ.extension r x
  domain := EY.domain ∩ EZ.domain
  open_domain := EY.open_domain.inter EZ.open_domain
  graph_mem s hs := ⟨EY.graph_mem s hs, EZ.graph_mem s hs⟩
  smooth z hz := by
    let A : Fin 2 → ℝ → (x : M) → TangentSpace (𝓡 n) x :=
      ![EY.extension, fun r x ↦ c • EZ.extension r x]
    have hY := (EY.smooth z hz.1).contMDiffAt (EY.open_domain.mem_nhds hz.1)
    have hZ := parametricExtension_contMDiffAt_smul_reparam EZ (f := id) hz.2
      contDiffAt_id (contDiffAt_const (c := c))
    have hA : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
          (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
            w.2 (A i w.1 w.2)) z := by
      intro i hi
      fin_cases i
      · exact hY
      · exact hZ
    have h := contMDiffAt_sum_parametric (Finset.univ : Finset (Fin 2)) A hA
    simpa only [A, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      h.contMDiffWithinAt
  agrees s hs := by rw [EY.agrees s hs, EZ.agrees s hs]

theorem pullbackCovariantDerivative_affine {J C : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) {α : ℝ → M} {Y Z : ∀ r, TangentSpace (𝓡 n) (α r)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EZ : ParametricAlongCurveExtensionOn C α Z) (c : ℝ)
    {s : ℝ} (hs : s ∈ C) :
    pullbackCovariantDerivative F time α (fun r ↦ Y r + c • Z r) C
        (affineParametricExtension EY EZ c) s =
      pullbackCovariantDerivative F time α Y C EY s +
        c • pullbackCovariantDerivative F time α Z C EZ s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hdy := (parametricExtension_differentiableAt_time EY (EY.graph_mem s hs)).hasDerivAt
  have hdz := (parametricExtension_differentiableAt_time EZ (EZ.graph_mem s hs)).hasDerivAt
  have hd := (hdy.add (hdz.const_smul c)).deriv
  have hY := (parametricExtension_contMDiffAt_space EY (EY.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hZ := (parametricExtension_contMDiffAt_space EZ (EZ.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hadd := (F.connection (time s)).connection.isCovariantDerivativeOn.add hY
    ((mdifferentiableAt_const (c := c)).smul_section hZ)
  have hsmul := (F.connection (time s)).connection.isCovariantDerivativeOn.smul_const c hZ
  change (F.connection (time s)).connection (EY.extension s + c • EZ.extension s) (α s) =
    (F.connection (time s)).connection (EY.extension s) (α s) +
      (F.connection (time s)).connection (c • EZ.extension s) (α s) at hadd
  change deriv (fun r ↦ EY.extension r (α s) + c • EZ.extension r (α s)) s =
    deriv (fun r ↦ EY.extension r (α s)) s + c • deriv (fun r ↦ EZ.extension r (α s)) s at hd
  rw [hsmul] at hadd
  change deriv (fun r ↦ EY.extension r (α s) + c • EZ.extension r (α s)) s +
    (F.connection (time s)).connection (EY.extension s + c • EZ.extension s) (α s)
      (curveVelocityWithin (n := n) α C s) = _
  rw [hd, hadd]
  simp only [pullbackCovariantDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_add]
  abel

theorem pullbackCovariantDerivative_affine_congr {J C : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) {α : ℝ → M} {Y Z H : ∀ r, TangentSpace (𝓡 n) (α r)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EZ : ParametricAlongCurveExtensionOn C α Z)
    (EH : ParametricAlongCurveExtensionOn C α H) (c : ℝ)
    (hH : ∀ s ∈ C, H s = Y s + c • Z s)
    {s : ℝ} (hs : s ∈ C) (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α H C EH s =
      pullbackCovariantDerivative F time α Y C EY s +
        c • pullbackCovariantDerivative F time α Z C EZ s := by
  rw [pullbackCovariantDerivative_congr F time (show EqOn α α C from fun _ _ ↦ rfl)
    hH EH (affineParametricExtension EY EZ c) hs hC hα]
  exact pullbackCovariantDerivative_affine F time EY EZ c hs

end PoincareConjecture.M08
