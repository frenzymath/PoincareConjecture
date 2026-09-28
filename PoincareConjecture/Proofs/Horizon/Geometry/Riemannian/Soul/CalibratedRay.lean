import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Filter Set Metric
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M] [ProperSpace M]

theorem exists_calibrated_ray (hsegments : HasMinimizingSegments M)
    {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    ∃ coray : ℝ → M, IsRay coray ∧ coray 0 = x ∧
      ∀ t : ℝ, 0 ≤ t → busemann ray (coray t) = busemann ray x - t := by
  classical
  choose curve hcurve0 hcurved hcurve using fun k : ℕ => hsegments x (ray k)
  have hexhaust : ∀ t ∈ Ici (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      t ∈ Icc 0 (dist x (ray k)) := by
    intro t ht
    filter_upwards [eventually_ge_atTop ⌈t + dist (ray 0) x⌉₊] with k hk
    have hd : dist (ray 0) (ray (k : ℝ)) = (k : ℝ) := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)] using
        hray le_rfl (Nat.cast_nonneg k)
    have htriangle := dist_triangle (ray 0) x (ray (k : ℝ))
    have hceil := (Nat.le_ceil (t + dist (ray 0) x)).trans (Nat.cast_le.mpr hk)
    rw [hd] at htriangle
    exact ⟨ht, by linarith⟩
  obtain ⟨coray, hcoray, hcoray0, hlimit⟩ := exists_minimizing_hyperfilter_limit
    (I := Ici 0) self_mem_Ici hcurve (fun _ => ⟨le_rfl, dist_nonneg⟩)
      hexhaust isCompact_singleton (fun k => show curve k 0 ∈ ({x} : Set M) from hcurve0 k)
  have hcoray0 : coray 0 = x := hcoray0
  refine ⟨coray, hcoray, hcoray0, ?_⟩
  intro t ht
  have hupper : busemann ray (coray t) ≤ busemann ray x - t := by
    have hleft := (lipschitz_busemann hray).continuous.continuousAt.tendsto.comp (hlimit t ht)
    have hright := ((tendsto_busemannApprox hray x).comp
      tendsto_natCast_atTop_atTop).sub (tendsto_const_nhds (x := t))
    apply le_of_tendsto_of_tendsto hleft (hright.mono_left Nat.hyperfilter_le_atTop)
    filter_upwards [(hexhaust t ht).filter_mono Nat.hyperfilter_le_atTop] with k hk
    have hd := hcurve k hk (show dist x (ray k) ∈ Icc 0 (dist x (ray k)) from
      ⟨dist_nonneg, le_rfl⟩)
    rw [hcurved k, abs_of_nonpos (sub_nonpos.mpr hk.2), neg_sub] at hd
    have h := busemann_le_approx hray (curve k t) (Nat.cast_nonneg k)
    dsimp [busemannApprox] at h ⊢
    rw [dist_comm (ray (k : ℝ)) (curve k t), hd, dist_comm x (ray (k : ℝ))] at h
    linarith
  have hlower : busemann ray x - t ≤ busemann ray (coray t) := by
    have hd : dist x (coray t) = t := by
      simpa only [hcoray0, zero_sub, abs_neg, abs_of_nonneg ht] using
        hcoray self_mem_Ici ht
    have h := (lipschitz_busemann hray).le_add_mul x (coray t)
    rw [NNReal.coe_one, one_mul, hd] at h
    linarith
  exact le_antisymm hupper hlower

end Poincare.Riemannian.Soul
