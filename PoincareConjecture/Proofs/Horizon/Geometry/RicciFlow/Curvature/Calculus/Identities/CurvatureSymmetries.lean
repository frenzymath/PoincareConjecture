import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarBracket








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem curvatureOnFields_metric_skew (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z W : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% W) U) {x : M} (hx : x ∈ U) :
    g.inner x (D.curvatureOnFields X Y Z x) (W x) =
      -g.inner x (D.curvatureOnFields X Y W x) (Z x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![X, Y]
  let S : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := ![Z, W]
  have hV (i : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (V i)) U := by
    fin_cases i
    · exact hX
    · exact hY
  have hS (j : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (S j)) U := by
    fin_cases j
    · exact hZ
    · exact hW
  let A (i j : Fin 2) := fun y ↦ D.connection (S j) y (V i y)
  have hA (i j : Fin 2) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (A i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (A i j)
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      ((hV i).mono Set.inter_subset_left) ((hS j).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  have hSD (j : Fin 2) :=
    (((hS j) x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hAD (i j : Fin 2) :=
    (((hA i j) x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  let F := fun y ↦ g.inner y (Z y) (W y)
  let VF (i : Fin 2) := fun y ↦ mvfderiv (𝓡 n) F y (V i y)
  let L (i : Fin 2) := fun y ↦ g.inner y (A i 0 y) (W y)
  let K (i : Fin 2) := fun y ↦ g.inner y (Z y) (A i 1 y)
  have hL (i : Fin 2) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (L i) U :=
    (hA i 0).inner_bundle hW
  have hK (i : Fin 2) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (K i) U :=
    hZ.inner_bundle (hA i 1)
  have hF : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F U := hZ.inner_bundle hW
  have hE (i : Fin 2) : VF i =ᶠ[𝓝 x] (fun y ↦ L i y + K i y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact metric_derivative_pairing D (V i)
      ((hZ y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
      ((hW y hy).contMDiffAt (hU.mem_nhds hy) |>.mdifferentiableAt (by simp))
  have hDE (i j : Fin 2) : mvfderiv (𝓡 n) (VF i) x (V j x) =
      g.inner x (D.connection (A i 0) x (V j x)) (W x) +
      g.inner x (A i 0 x) (A j 1 x) +
      (g.inner x (A j 0 x) (A i 1 x) +
        g.inner x (Z x) (D.connection (A i 1) x (V j x))) := by
    have heq : mvfderiv (𝓡 n) (VF i) x =
        mvfderiv (𝓡 n) (fun y ↦ L i y + K i y) x := (hE i).mfderiv_eq
    rw [heq]
    erw [mvfderiv_add
      (((hL i) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
      (((hK i) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)), add_apply]
    exact congrArg₂ (fun a b : ℝ ↦ a + b)
      (metric_derivative_pairing D (V j) (hAD i 0) (hSD 1))
      (metric_derivative_pairing D (V j) (hSD 0) (hAD i 1))
  have hcomm := mvfderiv_mlieBracket hU hF hX hY hx
  have hb := metric_derivative_pairing D (VectorField.mlieBracket (𝓡 n) X Y)
    (hSD 0) (hSD 1)
  change mvfderiv (𝓡 n) F x (VectorField.mlieBracket (𝓡 n) X Y x) =
    mvfderiv (𝓡 n) (VF 1) x (V 0 x) - mvfderiv (𝓡 n) (VF 0) x (V 1 x) at hcomm
  rw [hDE 1 0, hDE 0 1] at hcomm
  erw [hb] at hcomm
  have hsym (v : TangentSpace (𝓡 n) x) : g.inner x (Z x) v = g.inner x v (Z x) :=
    g.symm x _ _
  simp only [hsym, A, V, S, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hcomm
  simp only [LeviCivitaData.curvatureOnFields, map_sub, sub_apply]
  linarith only [hcomm]

theorem curvatureTensor_swap_last (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = -D.curvatureTensor x u v z w := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  simpa only [LeviCivitaData.curvatureTensor, LeviCivitaData.curvature,
    FiberBundle.extend_apply_self] using
    curvatureOnFields_metric_skew D t.open_baseSet
      (contMDiffOn_extend_baseSet u) (contMDiffOn_extend_baseSet v)
      (contMDiffOn_extend_baseSet z) (contMDiffOn_extend_baseSet w)
      (FiberBundle.mem_baseSet_trivializationAt' x)

theorem curvatureTensor_cyclic (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z + D.curvatureTensor x v w u z +
      D.curvatureTensor x w u v z = 0 := by
  have h := congrArg (fun a ↦ g.inner x a z) (curvature_cyclic D x u v w)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  change D.curvatureTensor x u v z w + D.curvatureTensor x v w z u +
    D.curvatureTensor x w u z v = 0 at h
  rw [curvatureTensor_swap_last D x u v z w,
    curvatureTensor_swap_last D x v w z u, curvatureTensor_swap_last D x w u z v] at h
  linarith only [h]

theorem curvatureTensor_pair_exchange (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z = D.curvatureTensor x w z u v := by
  have h1 := curvatureTensor_cyclic D x u v w z
  have h2 := curvatureTensor_cyclic D x u v z w
  have h3 := curvatureTensor_cyclic D x w z u v
  have h4 := curvatureTensor_cyclic D x v w z u
  rw [curvatureTensor_swap_last D x u v z w] at h2
  rw [curvatureTensor_swap_last D x z u w v,
    curvatureTensor_swap_last D x u w z v,
    curvatureTensor_swap_first D x w u v z, neg_neg] at h3
  rw [curvatureTensor_swap_last D x v w z u,
    curvatureTensor_swap_last D x w z v u,
    curvatureTensor_swap_last D x z v w u,
    curvatureTensor_swap_first D x v z u w, neg_neg] at h4
  linarith only [h1, h2, h3, h4]

theorem ricci_symm (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D.ricci x v u := by
  unfold LeviCivitaData.ricci
  apply Finset.sum_congr rfl
  intro i _
  exact curvatureTensor_pair_exchange D x u _ v _

end PoincareConjecture.RicciFlowAnalysis
