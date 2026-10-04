import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Gauss.MapConnection
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Data

/-!
# The actual source connection trace in conformal disk coordinates

Koszul's formula and the genuine metric germ give the dimension-two
cancellation. Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, twelfth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M65Gauss

/-- The Euclidean trace of the actual Levi-Civita coefficient vanishes for
a genuinely conformal two-dimensional metric germ. Source: MT Lemma 19.2,
p. 438; derivation 24, twelfth stage. -/
theorem connectionCoefficient_trace_eq_zero
    {h : RiemannianMetric 2 LoopPlane} (D : LeviCivitaData h)
    {x : LoopPlane} {c : LoopPlane → ℝ}
    (hconf : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      h.inner y (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c y else 0) :
    (∑ i : Fin 2, connectionCoefficient D x
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let S : LoopPlane := connectionCoefficient D x (e 0) (e 0) +
    connectionCoefficient D x (e 1) (e 1)
  have hp (i j k : Fin 2) :
      fderiv ℝ (fun y => h.inner y (e i) (e j)) x (e k) =
        if i = j then fderiv ℝ c x (e k) else 0 := by
    have he : (fun y => h.inner y (e i) (e j)) =ᶠ[𝓝 x]
        (fun y => if i = j then c y else 0) := hconf.mono fun y hy => hy i j
    rw [he.fderiv_eq]
    split_ifs <;> simp
  have hpair (k : Fin 2) : h.inner x S (e k) = 0 := by
    have h0 := D.inner_connection_const x (e 0) (e 0) (e k)
    have h1 := D.inner_connection_const x (e 1) (e 1) (e k)
    change 2 * h.inner x (connectionCoefficient D x (e 0) (e 0)) (e k) = _ at h0
    change 2 * h.inner x (connectionCoefficient D x (e 1) (e 1)) (e k) = _ at h1
    rw [hp, hp, hp] at h0 h1
    dsimp only [S]
    simp only [map_add, add_apply]
    fin_cases k <;> norm_num at h0 h1 ⊢ <;> linarith
  have hnorm : h.inner x S S = 0 := by
    have he : S = ∑ i : Fin 2, e.repr S i • e i := (e.sum_repr S).symm
    nth_rw 2 [he]
    simp only [map_sum, map_smul, hpair, smul_zero, Finset.sum_const_zero]
  have hS : S = 0 := by
    by_contra hn
    exact (h.pos x S hn).ne' hnorm
  simpa only [Fin.sum_univ_two, e, S] using hS

end PoincareMT.M65Gauss
