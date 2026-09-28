import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open PoincareConjecture Filter Set VectorField
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem connection_gradient_eq_id
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {u : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hess : ∀ x (v w : TangentSpace (𝓡 n) x), D.hessian u x v w = g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.connection (D.gradient u) x v = v := by
  apply (g.inner_isInvertible x).injective
  ext w
  rw [← D.hessian_eq_inner_connection_gradient (hu x), hess]

theorem radial_gradient_pushforward_smooth_and_mfderiv
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {F : M → EuclideanSpace ℝ (Fin n)}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hess : ∀ x (v w : TangentSpace (𝓡 n) x), D.hessian u x v w = g.inner x v w) :
    let V : M → EuclideanSpace ℝ (Fin n) :=
      fun x => mfderiv (𝓡 n) (𝓡 n) F x (D.gradient u x)
    ContMDiff (𝓡 n) (𝓡 n) ∞ V ∧
      ∀ x, mfderiv (𝓡 n) (𝓡 n) V x = mfderiv (𝓡 n) (𝓡 n) F x := by
  let V : M → EuclideanSpace ℝ (Fin n) :=
    fun x => mfderiv (𝓡 n) (𝓡 n) F x (D.gradient u x)
  let gE := RiemannianMetric.euclideanMetric n
  let DE := gE.euclideanLeviCivitaData
  have hlocal (x : M) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ V x ∧
      mfderiv (𝓡 n) (𝓡 n) V x = mfderiv (𝓡 n) (𝓡 n) F x := by
    let e := (hF x).localInverse
    let Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      mpullback (𝓡 n) (𝓡 n) e (D.gradient u)
    have he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (F x) := (hF x).localInverse_contMDiffAt
    have hei (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ e.source) :
        (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible :=
      ⟨(e.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hy).mfderivToContinuousLinearEquiv
        (by simp), rfl⟩
    have hinv : ∀ᶠ y in 𝓝 (F x), (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible :=
      Filter.mem_of_superset (e.open_source.mem_nhds (hF x).localInverse_mem_source) hei
    have hemetric : ∀ᶠ y in 𝓝 (F x), ∀ v w : EuclideanSpace ℝ (Fin n),
        gE.inner y v w = g.inner (e y) (mfderiv (𝓡 n) (𝓡 n) e y v)
          (mfderiv (𝓡 n) (𝓡 n) e y w) := by
      filter_upwards [e.open_source.mem_nhds (hF x).localInverse_mem_source] with y hy v w
      have heq : F ∘ e =ᶠ[𝓝 y] id :=
        Filter.mem_of_superset (e.open_source.mem_nhds hy) (hF x).localInverse_eqOn_right
      have hd := mfderiv_comp y (hF.mdifferentiable (by simp) (e y))
        ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
      rw [heq.mfderiv_eq, mfderiv_id] at hd
      rw [hmetric]
      have hv := congrArg (fun L => L v) hd
      have hw := congrArg (fun L => L w) hd
      exact congrArg₂ (inner ℝ) hv hw
    have hYbundle : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (E := TangentSpace (𝓡 n)) (Y y)) (F x) :=
      (D.contMDiffAt_gradient (hu (e (F x)))).mpullback_vectorField_preimage
        he hinv.self_of_nhds (by simp)
    have hY : ContMDiffAt (𝓡 n) (𝓡 n) ∞ Y (F x) := by
      rw [Bundle.contMDiffAt_totalSpace] at hYbundle
      simpa using hYbundle.2
    have hYd : DifferentiableAt ℝ Y (F x) :=
      (contMDiffAt_iff_contDiffAt.mp hY).differentiableAt (by simp)
    have hDY (v : EuclideanSpace ℝ (Fin n)) : fderiv ℝ Y (F x) v = v := by
      have hconn := DE.connection_mpullback_of_metric_pullback D he hinv hemetric
        ((D.contMDiffAt_gradient (hu (e (F x)))).mdifferentiableAt (by simp)) v
      rw [connection_gradient_eq_id D hu hess, hinv.self_of_nhds.inverse_apply_self] at hconn
      change DE.connection Y (F x) v = v at hconn
      rw [DE.connection_eq_fderiv_add hYd] at hconn
      unfold LeviCivitaData.euclideanConnection at hconn
      rw [DE.connection_const_eq_inverse] at hconn
      have hzero : fderiv ℝ gE.euclideanCoefficients (F x) = 0 := by
        change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ) (F x) = 0
        exact fderiv_const_apply _
      rw [hzero] at hconn
      simpa [metricKoszulCovector] using hconn
    have hnear : V =ᶠ[𝓝 x] Y ∘ F := by
      filter_upwards [(hF x).localInverse_eventuallyEq_left.eventually_nhds,
        hF.contMDiff.continuous.continuousAt.eventually
          (e.open_source.mem_nhds (hF x).localInverse_mem_source)] with y hleft hy
      have hleft' : e ∘ F =ᶠ[𝓝 y] id := hleft
      have hd := mfderiv_comp y
        ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
        (hF.mdifferentiable (by simp) y)
      rw [hleft'.mfderiv_eq, mfderiv_id] at hd
      change mfderiv (𝓡 n) (𝓡 n) F y (D.gradient u y) =
        (mfderiv (𝓡 n) (𝓡 n) e (F y)).inverse (D.gradient u (e (F y)))
      have hleftvalue : e (F y) = y := hleft'.self_of_nhds
      symm
      apply (hei (F y) hy).inverse_apply_eq.mpr
      have hg : (show EuclideanSpace ℝ (Fin n) from D.gradient u y) =
          D.gradient u (e (F y)) :=
        congrArg (fun q : M => (show EuclideanSpace ℝ (Fin n) from D.gradient u q)) hleftvalue.symm
      exact ((congrArg (fun L => L (D.gradient u y)) hd).symm.trans hg).symm
    refine ⟨(hY.comp x (hF.contMDiff x)).congr_of_eventuallyEq hnear, ?_⟩
    rw [hnear.mfderiv_eq, mfderiv_comp x (hY.mdifferentiableAt (by simp))
      (hF.mdifferentiable (by simp) x)]
    ext v
    rw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    exact hDY _
  exact ⟨fun x => (hlocal x).1, fun x => (hlocal x).2⟩

theorem exists_unit_umbilic_of_radial_potential
    {m : ℕ} {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) S] [IsManifold (𝓡 m) ∞ S]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {F : M → EuclideanSpace ℝ (Fin n)}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 n) x), g.inner x v w =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hess : ∀ x (v w : TangentSpace (𝓡 n) x), D.hessian u x v w = g.inner x v w)
    {b : S → M} (hb : ContMDiff (𝓡 m) (𝓡 n) ∞ b)
    (hunit : ∀ z, g.inner (b z) (D.gradient u (b z)) (D.gradient u (b z)) = 1) :
    ∃ N : S → EuclideanSpace ℝ (Fin n), ContMDiff (𝓡 m) (𝓡 n) ∞ N ∧
      (∀ z, N z = mfderiv (𝓡 n) (𝓡 n) F (b z) (D.gradient u (b z))) ∧
      (∀ z, ‖N z‖ = 1) ∧
      ∀ z, mfderiv (𝓡 m) (𝓡 n) N z = mfderiv (𝓡 m) (𝓡 n) (F ∘ b) z := by
  obtain ⟨hV, hdV⟩ := radial_gradient_pushforward_smooth_and_mfderiv D hF hmetric hu hess
  let V : M → EuclideanSpace ℝ (Fin n) :=
    fun x => mfderiv (𝓡 n) (𝓡 n) F x (D.gradient u x)
  refine ⟨V ∘ b, hV.comp hb, fun _ => rfl, ?_, ?_⟩
  · intro z
    have h := hunit z
    rw [hmetric] at h
    change inner ℝ (V (b z)) (V (b z)) = 1 at h
    rw [real_inner_self_eq_norm_sq] at h
    change ‖V (b z)‖ = 1
    nlinarith [norm_nonneg (V (b z))]
  · intro z
    rw [mfderiv_comp z (hV.mdifferentiable (by simp) (b z)) (hb.mdifferentiable (by simp) z),
      mfderiv_comp z (hF.mdifferentiable (by simp) (b z)) (hb.mdifferentiable (by simp) z), hdV]

end Poincare.Geometry.Riemannian.Hypersurface
