import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.NullPlane
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.SupportingLaplacian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Reaction
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T2Space M] in

theorem curvatureTensor_radial_eq_zero_of_null_plane
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hsec : ∀ u z : TangentSpace (𝓡 n) x,
      0 ≤ D.curvatureTensor x u z u z)
    {v w : TangentSpace (𝓡 n) x}
    (hzero : D.curvatureTensor x v w v w = 0)
    (z : TangentSpace (𝓡 n) x) : D.curvatureTensor x z w v w = 0 := by
  let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    D.curvatureTensor_bilinear_first_third x w w
  have hsym : LinearMap.IsSymm B := ⟨fun u z => (hD.2.2.2.1 x u w z w).2.1⟩
  have hk := (B.apply_apply_same_eq_zero_iff (fun u => hsec u w) hsym).mp hzero
  have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hk) z
  change D.curvatureTensor x v w z w = 0 at h
  rwa [(hD.2.2.2.1 x v w z w).2.1] at h

omit [T2Space M] in

theorem curvatureReaction_null_plane_eq_curvatureB
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hsec : ∀ u z : TangentSpace (𝓡 n) x,
      0 ≤ D.curvatureTensor x u z u z)
    {v w : TangentSpace (𝓡 n) x}
    (hzero : D.curvatureTensor x v w v w = 0) :
    D.curvatureReaction x v w v w =
      2 * (D.curvatureB x v w v w - D.curvatureB x v w w v -
        D.curvatureB x v w w v + D.curvatureB x v v w w) := by
  have hswap : D.curvatureTensor x w v w v = 0 := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg, hzero]
  have hfirst (z) := D.curvatureTensor_radial_eq_zero_of_null_plane hD x hsec hzero z
  have hthird (z) : D.curvatureTensor x v w z w = 0 := by
    rw [(hD.2.2.2.1 x v w z w).2.1, hfirst]
  have hsecond (z) : D.curvatureTensor x v z v w = 0 := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    exact D.curvatureTensor_radial_eq_zero_of_null_plane hD x hsec hswap z
  have hlast (z) : D.curvatureTensor x v w v z = 0 := by
    rw [(hD.2.2.2.1 x v w v z).2.1, hsecond]
  have h := D.movingInput_curvatureB_reaction hD x v w v w
  simpa only [hfirst, hsecond, hthird, hlast, add_zero] using h

theorem tensorLaplacian_nonneg_on_null_plane
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hsec : D.NonnegativeSectionalCurvature)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : D.curvatureTensor x v w v w = 0) :
    0 ≤ D.tensorLaplacian D.riemannEvaluation x ![v, w, v, w] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨r, Y, hr, -, hY, hinit, -, hfirst, hsecond, -⟩ :=
    D.exists_radialParallelIsometries_with_jets x
  let U := LeviCivitaData.radialNeighborhood (n := n) x r
  let V : (y : M) → TangentSpace (𝓡 n) y :=
    LeviCivitaData.fieldFromCenteredCoordinates x (Y v)
  let W : (y : M) → TangentSpace (𝓡 n) y :=
    LeviCivitaData.fieldFromCenteredCoordinates x (Y w)
  have hU : IsOpen U := LeviCivitaData.isOpen_radialNeighborhood x r
  have hxU : x ∈ U := LeviCivitaData.mem_radialNeighborhood x hr
  have hs (z : TangentSpace (𝓡 n) x) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (T% (LeviCivitaData.fieldFromCenteredCoordinates x (Y z))) U := by
    intro y hy
    exact (LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates x
      (hY z).contDiffAt hy.1).contMDiffWithinAt
  have hmax : IsLocalMax (fun y => ∑ _j : Fin 1, (-1 : ℝ) *
      D.riemannEvaluation y (fun i => ![V, W, V, W] i y)) x := by
    filter_upwards [] with y
    simp only [Fin.sum_univ_one, neg_one_mul]
    change -D.curvatureTensor y (V y) (W y) (V y) (W y) ≤
      -D.curvatureTensor x (V x) (W x) (V x) (W x)
    rw [show V x = v from hinit v, show W x = w from hinit w, hzero, neg_zero]
    exact neg_nonpos.mpr (hsec y _ _)
  have h := D.sum_tensorLaplacian_nonpos_of_isLocalMax
    (J := Fin 1) (k := 4) hD.1 (fun _ => (-1 : ℝ))
    (fun _ => ![V, W, V, W]) hU
    (by intro j i; fin_cases i <;> exact hs _) hxU
    (by intro j i a; fin_cases i <;> exact hfirst _ a)
    (by intro j i a; fin_cases i <;> exact hsecond _ a) hmax
  have htuple : (fun i => ![V, W, V, W] i x) = ![v, w, v, w] := by
    ext i
    fin_cases i <;> exact hinit _
  simpa only [Fin.sum_univ_one, htuple, neg_one_mul, neg_nonpos] using h

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

theorem curvatureReaction_nonpos_on_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    (F.connection 0).curvatureReaction x v w v w ≤ 0 := by
  have hlap := (F.connection 0).tensorLaplacian_nonneg_on_null_plane
    (hC.tensor_calculus n M (F.metric 0) (F.connection 0))
    (fun y u z => (F.connection 0).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hoperator 0 le_rfl y) u z) x v w hzero
  have hevol := F.curvatureEvolution_nonpos_on_terminal_null_plane hC hoperator x v w hzero
  linarith

end PoincareConjecture.RicciFlow
