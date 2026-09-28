import PoincareConjecture.Proofs.M03.ConnectionFamily
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem localFrame_covariant_derivative_coordinate
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x₀ : M)
    (W : (y : M) → TangentSpace (𝓡 n) y) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x₀
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := fun (i : Fin n) (y : M) =>
      e.localFrameCoeff (𝓡 n) b i y
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet →
    ∀ {x : M} (hx : x ∈ e.baseSet) (i l : Fin n),
      theta l x (D.connection W x (E i x)) =
        mvfderiv (𝓡 n) (fun y => theta l y (W y)) x (E i x) +
          ∑ p, theta l x (D.connection (E p) x (E i x)) *
            theta p x (W x) := by
  classical
  dsimp only
  intro hW x hx i l
  let V := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x₀).baseSet
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x₀
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let θ := e.localFrameCoeff (𝓡 n) b
  let q := fun (j : Fin n) (Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    θ j y (Y y)
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  have hV : IsOpen V := e.open_baseSet
  have hxV : x ∈ V := hx
  let S := fun Y : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) V
  have hWS : S W := hW
  have hmd (Y : (y : M) → TangentSpace (𝓡 n) y) (hY : S Y)
      {y : M} (hy : y ∈ V) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) y :=
    (hY.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hV A B hA hB
  have hE (j : Fin n) : S (E j) := by
    exact (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b j)
  have hEvalue (j : Fin n) {y : M} (hy : y ∈ V) :
      E j y = e.basisAt b hy j :=
    e.localFrame_apply_of_mem_baseSet b hy
  have hθrepr (Y : (y : M) → TangentSpace (𝓡 n) y) (j : Fin n)
      {y : M} (hy : y ∈ V) :
      θ j y (Y y) = (e.basisAt b hy).repr (Y y) j :=
    e.localFrameCoeff_apply_of_mem_baseSet b hy Y j
  have hq (j : Fin n) (Y : (y : M) → TangentSpace (𝓡 n) y)
      (hY : S Y) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q j Y) V :=
    contMDiffOn_localFrameCoeff b hV subset_rfl hY j
  have hqmd (j : Fin n) (Y : (y : M) → TangentSpace (𝓡 n) y)
      (hY : S Y) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (q j Y) x :=
    ((hq j Y hY).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
  have hrec (Y : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ V) : Y y = ∑ j, q j Y y • E j y := by
    simpa only [q, hθrepr Y _ hy, hEvalue _ hy] using
      ((e.basisAt b hy).sum_repr (Y y)).symm
  have hθself (j k : Fin n) : θ j x (E k x) = if k = j then 1 else 0 := by
    rw [hθrepr (E k) j hxV, hEvalue k hxV]
    exact Module.Basis.repr_self_apply _ _ _
  have hc := D.connection.isCovariantDerivativeOn (s := Set.univ)
  have hnsum (Y : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hY : ∀ j, MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (Y j)) x)
      (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ j, Y j y) x v = ∑ j, D.connection (Y j) x v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ j ∈ s, Y j y) x v =
          ∑ j ∈ s, D.connection (Y j) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, zero_apply]
      | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        change D.connection (Y j + fun y => ∑ k ∈ s, Y k y) x v = _
        rw [hc.add (hY j) (MDifferentiableAt.sum_section fun k _ => hY k),
          add_apply, ih]
    exact aux Finset.univ
  have hNW (A Y : (y : M) → TangentSpace (𝓡 n) y) (hY : S Y) :
      N A Y x = ∑ j, (q j Y x • N A (E j) x +
        mvfderiv (𝓡 n) (q j Y) x (A x) • E j x) := by
    have hs (j : Fin n) : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% ((q j Y) • E j)) x :=
      (hqmd j Y hY).smul_section (hmd _ (hE j) hxV)
    have heq := hc.congr_of_eventuallyEq (hmd Y hY hxV)
      (MDifferentiableAt.sum_section fun j _ => hs j) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) fun y hy => hrec Y hy)
    calc
      _ = D.connection (fun y => ∑ j, q j Y y • E j y) x (A x) :=
        congrArg (fun T => T (A x)) heq
      _ = ∑ j, D.connection ((q j Y) • E j) x (A x) :=
        hnsum (fun j => (q j Y) • E j) hs (A x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [N, add_apply, smul_apply,
          ContinuousLinearMap.smulRight_apply] using
          congrArg (fun T => T (A x))
            (hc.leibniz (hmd _ (hE j) hxV) (hqmd j Y hY))
  have hcoeff (A Y : (y : M) → TangentSpace (𝓡 n) y) (hY : S Y) (j : Fin n) :
      θ j x (N A Y x) = mvfderiv (𝓡 n) (q j Y) x (A x) +
        ∑ k, q k Y x * θ j x (N A (E k) x) := by
    rw [hNW A Y hY]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, hθself,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ j)]
    exact add_comm _ _
  simpa only [N, q, E, θ, mul_comm] using hcoeff (E i) W hWS l

end PoincareConjecture.Proofs.M03
