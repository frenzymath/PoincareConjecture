import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Time
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ClassicalEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

private theorem heatKernelContinuousTime_eq_fixed (a : ℝ) (ha : 0 < a)
    (s : ℝ) (has : a < s) (x y : M) :
    heatKernelContinuousTime D S s x y =
      heatPowerContinuousTime D S 0 (s - a)
        (evaluationRow (heatPowerContinuous D S 0 a ha) y) x := by
  rw [heatKernelContinuousTime_of_pos D S (ha.trans has),
    heatPowerContinuousTime_of_pos D S 0 (sub_pos.mpr has)]
  simpa only [sub_add_cancel] using
    heatKernelContinuous_add_eq_heatPowerContinuous D S (s - a) a (sub_pos.mpr has) ha x y

private theorem hasDerivAt_heatKernelContinuousTime_fixed (t : ℝ) (ht : 0 < t) (x y : M) :
    HasDerivAt (fun s => heatKernelContinuousTime D S s x y)
      (-heatPowerContinuousTime D S 1 (t - t / 2)
        (evaluationRow (heatPowerContinuous D S 0 (t / 2) (half_pos ht)) y) x) t := by
  let a := t / 2
  have ha : 0 < a := half_pos ht
  have hat : a < t := half_lt_self ht
  have hta : 0 < t - a := sub_pos.mpr hat
  let w := evaluationRow (heatPowerContinuous D S 0 a ha) y
  have hT : HasDerivAt (fun s : ℝ => heatPowerContinuousTime D S 0 (s - a))
      (-heatPowerContinuousTime D S 1 (t - a)) t := by
    have h := hasDerivAt_heatPowerContinuousTime D S 0 hta
    convert! h.scomp (F := Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ)) t
      ((hasDerivAt_id t).sub_const a) using 1
    simp only [one_smul]
  have hd : HasDerivAt (fun s : ℝ => heatPowerContinuousTime D S 0 (s - a) w x)
      (-heatPowerContinuousTime D S 1 (t - a) w x) t := by
    have h := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
      (hT.clm_apply (hasDerivAt_const t w))
    convert! h using 1
    simp
  have heq : (fun s => heatKernelContinuousTime D S s x y) =ᶠ[𝓝 t]
      fun s => heatPowerContinuousTime D S 0 (s - a) w x := by
    filter_upwards [Ioi_mem_nhds hat] with s hs
    exact heatKernelContinuousTime_eq_fixed D S a ha s hs x y
  exact hd.congr_of_eventuallyEq heq

theorem hasDerivAt_heatKernelContinuousTime_laplacian
    (t : ℝ) (ht : 0 < t) (x y : M) (hx : x ∈ Ω) :
    HasDerivAt (fun s => heatKernelContinuousTime D S s x y)
      (D.laplacian (fun z => heatKernelContinuousTime D S t z y) x) t := by
  have ha : 0 < t / 2 := half_pos ht
  have hta : 0 < t - t / 2 := sub_pos.mpr (half_lt_self ht)
  have hfun : (fun z => heatKernelContinuousTime D S t z y) =
      fun z => heatPowerContinuous D S 0 (t - t / 2) hta
        (evaluationRow (heatPowerContinuous D S 0 (t / 2) ha) y) z := by
    funext z
    rw [heatKernelContinuousTime_eq_fixed D S (t / 2) ha t (half_lt_self ht) z y,
      heatPowerContinuousTime_of_pos D S 0 hta]
  rw [hfun, heatPowerContinuous_laplacian D S 0 (t - t / 2) hta _ x hx]
  have hd := hasDerivAt_heatKernelContinuousTime_fixed D S t ht x y
  rw [heatPowerContinuousTime_of_pos D S 1 hta] at hd
  exact hd

end PoincareConjecture.LeviCivitaData.Dirichlet
