import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

theorem Set.Finite.exists_planar_coordinates_injOn_fst
    {s : Set (ℝ × ℝ)} (hs : s.Finite) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), InjOn (fun x => (e x).1) s := by
  let slope : (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun p => (p.2.1 - p.1.1) / (p.1.2 - p.2.2)
  obtain ⟨t, ht⟩ := ((hs.prod hs).image slope).exists_notMem
  let swap := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  let skew := (ContinuousLinearEquiv.refl ℝ ℝ).skewProd
    (ContinuousLinearEquiv.refl ℝ ℝ) (t • ContinuousLinearMap.id ℝ ℝ)
  let e := (swap.trans skew).trans swap
  have he (q : ℝ × ℝ) : (e q).1 = q.1 + t * q.2 := rfl
  refine ⟨e, ?_⟩
  intro x hx y hy hxy
  change (e x).1 = (e y).1 at hxy
  rw [he, he] at hxy
  by_cases h : x.2 = y.2
  · apply Prod.ext _ h
    rw [h] at hxy
    exact add_right_cancel hxy
  · exfalso
    apply ht
    refine ⟨(x, y), ⟨hx, hy⟩, ?_⟩
    change (y.1 - x.1) / (x.2 - y.2) = t
    apply (div_eq_iff (sub_ne_zero.mpr h)).mpr
    nlinarith [hxy]
