import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.ConnectionVariation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_connection_vector (F : RicciFlow n M J)
    {U : Set M} {X Y : (y : M) → TangentSpace (𝓡 n) y}
    {t : ℝ} {x : M}
    (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (ht : t ∈ interior J) (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt
      (fun s ↦ (F.connection s).connection Y x (X x))
      (∑ i,
        (-D.covariantTensorDerivative D.ricciEvaluation
            x ![X x, Y x, b i] -
          D.covariantTensorDerivative D.ricciEvaluation
            x ![Y x, X x, b i] +
          D.covariantTensorDerivative D.ricciEvaluation
            x ![b i, X x, Y x]) • b i) t := by
  classical
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let a (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    -D.covariantTensorDerivative D.ricciEvaluation x ![X x, Y x, b i] -
      D.covariantTensorDerivative D.ricciEvaluation x ![Y x, X x, b i] +
      D.covariantTensorDerivative D.ricciEvaluation x ![b i, X x, Y x]
  change HasDerivAt (fun s ↦ (F.connection s).connection Y x (X x))
    (∑ i, a i • b i) t
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hxe : x ∈ U ∩ e.baseSet :=
    ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hc (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      HasDerivAt
        (fun s ↦ (F.metric t).inner x ((F.connection s).connection Y x (X x)) (b i))
        (a i) t := by
    have h := hasDerivAt_connection_pairing F (hU.inter e.open_baseSet)
      (hX.mono inter_subset_left) (hY.mono inter_subset_left)
      ((contMDiffOn_extend_baseSet (n := n) (M := M) (x := x) (b i)).mono
        inter_subset_right) ht hxe
    simpa only [FiberBundle.extend_apply_self] using h
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ (hc i).smul_const (b i))
  have heq (s : ℝ) :
      (∑ i, (F.metric t).inner x ((F.connection s).connection Y x (X x)) (b i) • b i) =
        (F.connection s).connection Y x (X x) := by
    change (∑ i, inner ℝ ((F.connection s).connection Y x (X x)) (b i) • b i) = _
    simpa only [real_inner_comm] using
      b.sum_repr' ((F.connection s).connection Y x (X x))
  exact hs.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ (heq s).symm)

end PoincareConjecture.RicciFlowAnalysis
