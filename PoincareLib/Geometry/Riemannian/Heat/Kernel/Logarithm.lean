import PoincareLib.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The logarithmic heat equation

The logarithm of a positive smooth heat solution satisfies
`f_t = laplacian f + |gradient f|^2` for the retained metric and connection.
This is the scalar calculation underlying the Li--Yau estimate used in
Chow et al., Part III, Proposition 26.49, printed p. 379.

The exponential-chain-rule argument corresponds to
`heatSolution_log_evolution` in Chow--Liao--Qin,
`Analysis/Parabolic/Harnack/LiYau.lean`, revision
`1b535dd102b94cc42b107cca27059687888f08b3`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
/-- Positivity and joint smoothness give joint smoothness of the logarithm. -/
lemma contMDiffAt_log_of_pos {u : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hu : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, x))
    (hpos : 0 < u (t, x)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p => Real.log (u p)) (t, x) :=
  (Real.contDiffAt_log.mpr hpos.ne').comp_contMDiffAt hu

/-- Taking the logarithm transforms the heat equation using the retained
Laplacian, without assuming regularity of the logarithm separately. -/
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

end PoincareMT.LeviCivitaData
