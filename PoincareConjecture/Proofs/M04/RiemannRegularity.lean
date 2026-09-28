import PoincareConjecture.Proofs.M04.CurvaturePointwise
import PoincareConjecture.Proofs.M04.CurvatureFieldsRegularity
import PoincareConjecture.Definitions.Ch01.TensorRegularity





set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem isSmoothCovariantTensor_riemannEvaluation (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.riemannEvaluation := by
  constructor
  · intro x
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let E := fun v : TangentSpace (𝓡 n) x ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    have hE (v : TangentSpace (𝓡 n) x) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (E v)) t.baseSet := contMDiffOn_extend_baseSet v
    have ha1 (u u' v w : TangentSpace (𝓡 n) x) :
        D.curvature x (u + u') v w = D.curvature x u v w + D.curvature x u' v w := by
      have h := curvatureOnFields_add_left D t.open_baseSet (hE u) (hE u') (hE v) (hE w) hx
      rw [curvatureOnFields_eq_curvature D t.open_baseSet
        ((hE u).add_section (hE u')) (hE v) (hE w) hx] at h
      simpa only [Pi.add_apply, E, FiberBundle.extend_apply_self,
        LeviCivitaData.curvature] using! h
    have hs1 (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
        D.curvature x (c • u) v w = c • D.curvature x u v w := by
      have h := curvatureOnFields_smul_left D t.open_baseSet
        (f := fun _ ↦ c) contMDiffOn_const (hE u) (hE v) (hE w) hx
      rw [curvatureOnFields_eq_curvature D t.open_baseSet
        (contMDiffOn_const.smul_section (hE u)) (hE v) (hE w) hx] at h
      simpa only [Pi.smul_apply', E, FiberBundle.extend_apply_self,
        LeviCivitaData.curvature] using! h
    have ha3 (u v w w' : TangentSpace (𝓡 n) x) :
        D.curvature x u v (w + w') = D.curvature x u v w + D.curvature x u v w' := by
      have h := curvatureOnFields_add_third D t.open_baseSet (hE u) (hE v) (hE w) (hE w') hx
      rw [curvatureOnFields_eq_curvature D t.open_baseSet
        (hE u) (hE v) ((hE w).add_section (hE w')) hx] at h
      simpa only [Pi.add_apply, E, FiberBundle.extend_apply_self,
        LeviCivitaData.curvature] using! h
    have hs3 (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
        D.curvature x u v (c • w) = c • D.curvature x u v w := by
      have h := curvatureOnFields_smul_third D t.open_baseSet
        (f := fun _ ↦ c) contMDiffOn_const (hE u) (hE v) (hE w) hx
      rw [curvatureOnFields_eq_curvature D t.open_baseSet
        (hE u) (hE v) (contMDiffOn_const.smul_section (hE w)) hx] at h
      simpa only [Pi.smul_apply', E, FiberBundle.extend_apply_self,
        LeviCivitaData.curvature] using! h
    have ha2 (u v v' w : TangentSpace (𝓡 n) x) :
        D.curvature x u (v + v') w = D.curvature x u v w + D.curvature x u v' w := by
      rw [curvature_swap D x (v + v') u w, ha1,
        curvature_swap D x v u w, curvature_swap D x v' u w]
      simp only [neg_add_rev]
      abel
    have hs2 (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
        D.curvature x u (c • v) w = c • D.curvature x u v w := by
      rw [curvature_swap D x (c • v) u w, hs1, curvature_swap D x v u w]
      simp only [smul_neg]
    refine ⟨MultilinearMap.mk' (R := ℝ) (D.riemannEvaluation x) ?_ ?_, fun _ ↦ rfl⟩
    · intro v i a b
      fin_cases i <;>
        simp [LeviCivitaData.riemannEvaluation, Function.update,
          LeviCivitaData.curvatureTensor, ha1, ha2, ha3, map_add, add_apply]
    · intro v i c a
      fin_cases i <;>
        simp [LeviCivitaData.riemannEvaluation, Function.update,
          LeviCivitaData.curvatureTensor, hs1, hs2, hs3, map_smul, smul_apply, smul_eq_mul]
  · intro U hU X hX
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := (contMDiffOn_curvatureOnFields D hU (hX 0) (hX 1) (hX 3)).inner_bundle (hX 2)
    apply h.congr
    intro x hx
    change g.inner x (D.curvature x (X 0 x) (X 1 x) (X 3 x)) (X 2 x) =
      g.inner x (D.curvatureOnFields (X 0) (X 1) (X 3) x) (X 2 x)
    rw [curvatureOnFields_eq_curvature D hU (hX 0) (hX 1) (hX 3) hx]

end PoincareConjecture.M04
