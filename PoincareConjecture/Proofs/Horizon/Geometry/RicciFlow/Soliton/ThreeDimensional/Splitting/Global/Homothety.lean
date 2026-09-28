import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.HomotheticMetricSlice

open RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g h : RiemannianMetric n M} {c : ℝ}

theorem ricci (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D'.ricci x u v = D.ricci (E.map x)
      (mfderiv (𝓡 n) (𝓡 n) E.map x u) (mfderiv (𝓡 n) (𝓡 n) E.map x v) := by
  rw [← rescaledMetric_ricci g D c hc]
  exact D'.ricci_eq_of_local_isometry (rescaledMetric_connection g D c hc)
    isOpen_univ E.map.contMDiff.contMDiffOn
    (fun y _ a b => E.inner_eq y a b) (mem_univ x) u v

theorem ricciNullity (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    RicciFlow.Splitting.ricciNullity D' x =
      RicciFlow.Splitting.ricciNullity D (E.map x) := by
  let L := (E.map.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hL_apply (z : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) E.map x z = L z := rfl
  have hL_symm (z : TangentSpace (𝓡 n) (E.map x)) :
      mfderiv (𝓡 n) (𝓡 n) E.map x (L.symm z) = z := by
    rw [hL_apply, L.apply_symm_apply]
  have hker : ricciKernel D (E.map x) = (ricciKernel D' x).map L.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel, mem_ricciKernel]
    constructor
    · intro hv w
      have hrel := E.ricci hc D D' x (L.symm v) w
      rw [hL_symm, hL_apply] at hrel
      rw [hrel]
      exact hv (L w)
    · intro hv w
      obtain ⟨z, rfl⟩ := L.surjective w
      have hz := hv z
      have hrel := E.ricci hc D D' x (L.symm v) z
      rw [hL_symm, hL_apply] at hrel
      rw [← hrel]
      exact hz
  unfold RicciFlow.Splitting.ricciNullity
  rw [hker, LinearEquiv.finrank_map_eq]

end PoincareConjecture.HomotheticMetricSlice
