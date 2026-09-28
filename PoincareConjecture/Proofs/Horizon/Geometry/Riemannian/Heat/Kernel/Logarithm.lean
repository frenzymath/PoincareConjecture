import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv















set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in

lemma contMDiffAt_log_of_pos {u : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hu : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, x))
    (hpos : 0 < u (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p => Real.log (u p)) (t, x) :=
  (Real.contDiffAt_log.mpr hpos.ne').comp_contMDiffAt hu



theorem hasDerivAt_log_heat (D : LeviCivitaData g)
    {u : ℝ × M → ℝ} {t : ℝ}
    (hu : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, x))
    (hpos : ∀ x, 0 < u (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) (x : M) :
    HasDerivAt (fun s => Real.log (u (s, x)))
      (D.laplacian (fun y => Real.log (u (t, y))) x +
        g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
          (D.gradient (fun y => Real.log (u (t, y))) x)) t := by
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Real.log (u (t, y))) :=
    fun y => (contMDiffAt_log_of_pos (hu y) (hpos y)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hexp := D.laplacian_comp hf Real.contDiff_exp x
  simp only [Real.deriv_exp, Function.comp_def] at hexp
  simp only [Real.exp_log (hpos _)] at hexp
  apply ((hheat x).log (hpos x).ne').congr_deriv
  apply (div_eq_iff (hpos x).ne').mpr
  rw [hexp]
  ring

end PoincareConjecture.LeviCivitaData
