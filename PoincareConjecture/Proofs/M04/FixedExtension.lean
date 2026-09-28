import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem extend_eq_transport {x y : M} (v : TangentSpace (𝓡 n) x)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x).baseSet) :
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y =
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x).continuousLinearEquivAt ℝ y hy).symm
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x).continuousLinearEquivAt ℝ x
        (FiberBundle.mem_baseSet_trivializationAt' x) v) := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  change t.symm y (t ⟨x, v⟩).2 =
    (t.continuousLinearEquivAt ℝ y hy).symm (t.continuousLinearEquivAt ℝ x hx v)
  rfl

theorem contMDiffOn_extend_baseSet {x : M} (v : TangentSpace (𝓡 n) x) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v))
      (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) x).baseSet := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let w := (t ⟨x, v⟩).2
  intro y hy
  rw [t.contMDiffWithinAt_section _ hy]
  have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun _ : M ↦ w) t.baseSet := contMDiffOn_const
  have hcoord : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun z ↦ (t ⟨z, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v z⟩).2)
      t.baseSet := hc.congr (fun z hz ↦ by
        change (t ⟨z, t.symm z w⟩).2 = (t ⟨x, v⟩).2
        simpa [w] using congrArg Prod.snd (t.apply_mk_symm hz w))
  exact hcoord y hy

theorem extend_add_on_baseSet {x y : M} (u v : TangentSpace (𝓡 n) x)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x).baseSet) :
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (u + v) y =
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u y +
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y := by
  simp only [extend_eq_transport _ hy, map_add]

theorem extend_smul_on_baseSet {x y : M} (a : ℝ) (v : TangentSpace (𝓡 n) x)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x).baseSet) :
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (a • v) y =
      a • FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y := by
  simp only [extend_eq_transport _ hy, map_smul]

end PoincareConjecture.M04
