import PoincareConjecture.Definitions.Ch01.Curvature
import PoincareConjecture.Proofs.M03.ConnectionRegularity










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_swap {g : RiemannianMetric n M}
    (D : LeviCivitaData g)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    D.curvatureOnFields X Y Z x = -D.curvatureOnFields Y X Z x := by
  delta LeviCivitaData.curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (I := 𝓡 n) (V := X) (W := Y)]
  simp only [map_neg]
  module

theorem curvatureOnFields_tensorial_first {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun X : (y : M) → TangentSpace (𝓡 n) y => D.curvatureOnFields X Y Z x) x := by
  let : IsManifold (𝓡 n) 2 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hconn := ((D.contMDiffOn_connection hU Z hZ).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hN (X : (y : M) → TangentSpace (𝓡 n) y)
      (hX : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% (fun y => D.connection Z y (X y))) x :=
    hconn.clm_bundle_apply hX
  have hc := D.connection.isCovariantDerivativeOn (s := Set.univ)
  constructor
  · intro f X hf hX
    have hNX : (fun y => D.connection Z y ((f • X) y)) =
        f • (fun y => D.connection Z y (X y)) := by
      funext y
      exact map_smul (D.connection Z y) (f y) (X y)
    delta LeviCivitaData.curvatureOnFields
    rw [hNX, hc.leibniz (hN X hX) hf,
      VectorField.mlieBracket_smul_left hf hX]
    simp only [Pi.smul_apply', map_smul, map_add,
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
    module
  · intro X X' hX hX'
    have hNX : (fun y => D.connection Z y ((X + X') y)) =
        (fun y => D.connection Z y (X y)) + (fun y => D.connection Z y (X' y)) := by
      funext y
      exact map_add (D.connection Z y) (X y) (X' y)
    delta LeviCivitaData.curvatureOnFields
    rw [hNX, hc.add (hN X hX) (hN X' hX'),
      VectorField.mlieBracket_add_left hX hX']
    simp only [Pi.add_apply, map_add, add_apply]
    module

theorem curvatureOnFields_tensorial_second {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Z : (x : M) → TangentSpace (𝓡 n) x)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Y : (y : M) → TangentSpace (𝓡 n) y => D.curvatureOnFields X Y Z x) x := by
  have h := curvatureOnFields_tensorial_first D hU X Z hZ hx
  constructor
  · intro f Y hf hY
    change D.curvatureOnFields X (f • Y) Z x = f x • D.curvatureOnFields X Y Z x
    rw [curvatureOnFields_swap D X (f • Y) Z x, h.smul hf hY,
      curvatureOnFields_swap D X Y Z x, smul_neg]
  · intro Y Y' hY hY'
    rw [curvatureOnFields_swap D X (Y + Y') Z x, h.add hY hY',
      curvatureOnFields_swap D X Y Z x, curvatureOnFields_swap D X Y' Z x, neg_add]

end PoincareConjecture.Proofs.M03
