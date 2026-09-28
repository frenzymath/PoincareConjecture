import PoincareConjecture.Proofs.M30.Thm11_1.LocalParallelTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.CoverCoordinate















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M30




theorem exists_prescribed_parallel_null_section_of_finite_terminal_local_isometry
    {n : ℕ} {N : Type u} {M : Type v}
    [TopologicalSpace N] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n N (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : N, ricciNullity (F.connection b) y = 1)
    {gM : RiemannianMetric n M} (DM : LeviCivitaData gM)
    {f : N → M} (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hmetric : ∀ y : N, ∀ v1 v2 : TangentSpace (𝓡 n) y,
      (F.metric b).inner y v1 v2 = gM.inner (f y)
        (mfderiv (𝓡 n) (𝓡 n) f y v1) (mfderiv (𝓡 n) (𝓡 n) f y v2))
    (x : N) (v : TangentSpace (𝓡 n) (f x))
    (hunit : gM.inner (f x) v v = 1)
    (hnull : ∀ w : TangentSpace (𝓡 n) (f x), DM.ricci (f x) v w = 0) :
    ∃ (W : Set M) (Z : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen W ∧ f x ∈ W ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) W ∧ Z (f x) = v ∧
      ∀ y ∈ W, gM.inner y (Z y) (Z y) = 1 ∧
        (∀ w : TangentSpace (𝓡 n) y, DM.ricci y (Z y) w = 0) ∧
        ∀ w : TangentSpace (𝓡 n) y, DM.connection Z y w = 0 := by
  let L := mfderiv (𝓡 n) (𝓡 n) f x
  have hL : L.IsInvertible :=
    ⟨(hf x).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  let vN := L.inverse v
  have hvN : L vN = v := hL.self_apply_inverse v
  have hunitN : (F.metric b).inner x vN vN = 1 := by
    calc
      (F.metric b).inner x vN vN = gM.inner (f x) (L vN) (L vN) := hmetric x vN vN
      _ = 1 := by rw [hvN]; exact hunit
  have hnullN : ∀ w : TangentSpace (𝓡 n) x, (F.connection b).ricci x vN w = 0 := by
    intro w
    calc
      (F.connection b).ricci x vN w = DM.ricci (f x) (L vN) (L w) :=
        (F.connection b).ricci_eq_of_local_isometry DM isOpen_univ hf.contMDiff.contMDiffOn
          (fun y _ v1 v2 => hmetric y v1 v2) (mem_univ x) vN w
      _ = 0 := by rw [hvN]; exact hnull _
  let pN : UnitRicciKernel (F.connection b) := ⟨⟨x, vN⟩, hunitN, hnullN⟩
  obtain ⟨U, V, hU, hx, hV, hVx, hn⟩ :=
    exists_local_parallel_unit_ricci_null_section_through hC hab F hsec hdim pN
  obtain ⟨W, Z, hW, hfx, hZ, hZfx, hgeometry⟩ :=
    exists_local_parallel_unit_null_section_of_local_isometry
      (F.connection b) DM hf hmetric hU hx V hV hn
  refine ⟨W, Z, hW, hfx, hZ, ?_, hgeometry⟩
  exact hZfx.trans ((congrArg L hVx).trans hvN)

end PoincareConjecture.M30
