import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold VectorField
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M30

theorem exists_local_parallel_unit_null_section_of_local_isometry
    {n : ℕ} {N : Type u} {M : Type v}
    [TopologicalSpace N] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ M]
    {gN : RiemannianMetric n N} {gM : RiemannianMetric n M}
    (DN : LeviCivitaData gN) (DM : LeviCivitaData gM)
    {f : N → M} (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hmetric : ∀ y, ∀ a b : TangentSpace (𝓡 n) y,
      gN.inner y a b = gM.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y a) (mfderiv (𝓡 n) (𝓡 n) f y b))
    {U : Set N} (hU : IsOpen U) {x : N} (hx : x ∈ U)
    (V : (y : N) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U)
    (hn : ∀ y ∈ U, gN.inner y (V y) (V y) = 1 ∧
      (∀ w, DN.ricci y (V y) w = 0) ∧ ∀ w, DN.connection V y w = 0) :
    ∃ (W : Set M) (Z : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen W ∧ f x ∈ W ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) W ∧
      Z (f x) = mfderiv (𝓡 n) (𝓡 n) f x (V x) ∧
      ∀ y ∈ W, gM.inner y (Z y) (Z y) = 1 ∧
        (∀ w, DM.ricci y (Z y) w = 0) ∧ ∀ w, DM.connection Z y w = 0 := by
  let e := (hf x).localInverse
  let k : M → N := e
  let T : Set M := e.source
  have hT : IsOpen T := e.open_source
  have hxT : f x ∈ T := (hf x).localInverse_mem_source
  have hkx : k (f x) = x := (hf x).localInverse_left_inv (hf x).localInverse_mem_target
  have hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k T := e.contMDiffOn_toFun
  have hks (y : M) (hy : y ∈ T) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ k y :=
    hk.contMDiffAt (hT.mem_nhds hy)
  have hinv (y : M) (hy : y ∈ T) : (mfderiv (𝓡 n) (𝓡 n) k y).IsInvertible :=
    ⟨(e.isLocalDiffeomorphAt _ _ _ hy).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hright (y : M) (hy : y ∈ T) : f (k y) = y :=
    (hf x).localInverse_right_inv hy
  have hderiv (y : M) (hy : y ∈ T) :
      (mfderiv (𝓡 n) (𝓡 n) f (k y)).comp (mfderiv (𝓡 n) (𝓡 n) k y) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) y) := by
    have hgerm : f ∘ k =ᶠ[𝓝 y] id := by
      filter_upwards [hT.mem_nhds hy] with z hz
      exact hright z hz
    rw [← mfderiv_comp y (hf.contMDiff.mdifferentiable (by simp) (k y))
      ((hks y hy).mdifferentiableAt (by simp)), hgerm.mfderiv_eq]
    exact mfderiv_id
  have hmetrick (y : M) (hy : y ∈ T) (a b : TangentSpace (𝓡 n) y) :
      gM.inner y a b = gN.inner (k y)
        (mfderiv (𝓡 n) (𝓡 n) k y a) (mfderiv (𝓡 n) (𝓡 n) k y b) := by
    have ha (v : TangentSpace (𝓡 n) y) :
        mfderiv (𝓡 n) (𝓡 n) f (k y) (mfderiv (𝓡 n) (𝓡 n) k y v) = v :=
      congrArg (fun L => L v) (hderiv y hy)
    have hm := hmetric (k y)
      (mfderiv (𝓡 n) (𝓡 n) k y a) (mfderiv (𝓡 n) (𝓡 n) k y b)
    rw [ha a, ha b, hright y hy] at hm
    exact hm.symm
  let W : Set M := T ∩ k ⁻¹' U
  have hW : IsOpen W := hk.continuousOn.isOpen_inter_preimage hT hU
  have hxW : f x ∈ W := ⟨hxT, by simpa only [mem_preimage, hkx] using hx⟩
  let Z := mpullback (𝓡 n) (𝓡 n) k V
  have hpush (y : M) (hy : y ∈ T) :
      mfderiv (𝓡 n) (𝓡 n) k y (Z y) = V (k y) :=
    (hinv y hy).self_apply_inverse _
  have hZ (y : M) (hy : y ∈ W) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) y :=
    (hV.contMDiffAt (hU.mem_nhds hy.2)).mpullback_vectorField_preimage
      (hks y hy.1) (hinv y hy.1) (by simp)
  refine ⟨W, Z, hW, hxW, fun y hy => (hZ y hy).contMDiffWithinAt, ?_, ?_⟩
  · apply ((e.isLocalDiffeomorphAt _ _ _ hxT).mfderivToContinuousLinearEquiv
      (by simp)).injective
    change mfderiv (𝓡 n) (𝓡 n) k (f x) (Z (f x)) =
      mfderiv (𝓡 n) (𝓡 n) k (f x) (mfderiv (𝓡 n) (𝓡 n) f x (V x))
    have hleft : mfderiv (𝓡 n) (𝓡 n) k (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x (V x)) = V x :=
      ((hf x).mfderivToContinuousLinearEquiv (by simp)).symm_apply_apply (V x)
    rw [hpush _ hxT, hleft, hkx]
  · intro y hy
    refine ⟨?_, ?_, ?_⟩
    · rw [hmetrick y hy.1, hpush y hy.1]
      exact (hn _ hy.2).1
    · intro w
      rw [DM.ricci_eq_of_local_isometry DN hW (hk.mono inter_subset_left)
        (fun z hz => hmetrick z hz.1) hy, hpush y hy.1]
      exact (hn _ hy.2).2.1 _
    · intro w
      have hi : ∀ᶠ z in 𝓝 y, (mfderiv (𝓡 n) (𝓡 n) k z).IsInvertible := by
        filter_upwards [hT.mem_nhds hy.1] with z hz
        exact hinv z hz
      have hm : ∀ᶠ z in 𝓝 y, ∀ a b : TangentSpace (𝓡 n) z,
          gM.inner z a b = gN.inner (k z)
            (mfderiv (𝓡 n) (𝓡 n) k z a) (mfderiv (𝓡 n) (𝓡 n) k z b) := by
        filter_upwards [hT.mem_nhds hy.1] with z hz
        exact hmetrick z hz
      change DM.connection (mpullback (𝓡 n) (𝓡 n) k V) y w = 0
      rw [DM.connection_mpullback_of_metric_pullback DN (hks y hy.1) hi hm
        ((hV.contMDiffAt (hU.mem_nhds hy.2)).mdifferentiableAt (by simp)) w,
        (hn _ hy.2).2.2, map_zero]

end PoincareConjecture.M30
