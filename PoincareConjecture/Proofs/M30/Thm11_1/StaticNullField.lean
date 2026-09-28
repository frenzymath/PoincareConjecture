import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.CoverCoordinate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def unitRicciKernelField (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D)) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    (p : UnitRicciKernel D) → TangentSpace (𝓡 n) p := by
  letI := unitRicciKernelChartedSpace D hc
  letI := unitRicciKernelIsManifold D hc
  exact fun p =>
    (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p).inverse p.1.snd

theorem unitRicciKernelField_projection (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D)) (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p
      (unitRicciKernelField D hc p) = p.1.snd := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  have hinv : (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p).IsInvertible :=
    ⟨(unitRicciKernelProjection_isLocalDiffeomorph D hc).mfderivToContinuousLinearEquiv
      (by simp) p, rfl⟩
  exact hinv.self_apply_inverse _

theorem unitRicciKernelField_geometry_of_local_parallel_sections
    (D : LeviCivitaData g) (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hdim : ∀ x : M, ricciNullity D x = 1)
    (hlocal : ∀ p : UnitRicciKernel D,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
        IsOpen U ∧ p.1.proj ∈ U ∧
        ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧
        V p.1.proj = p.1.snd ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          (∀ w, D.ricci y (V y) w = 0) ∧
          ∀ w, D.connection V y w = 0) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let g' := unitRicciKernelMetric D hc
    let X := unitRicciKernelField D hc
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) ∧
      (∀ p, g'.inner p (X p) (X p) = 1) ∧
      ∀ p, ∀ w : TangentSpace (𝓡 n) p, g'.leviCivitaData.connection X p w = 0 := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let g' := unitRicciKernelMetric D hc
  let X := unitRicciKernelField D hc
  let proj := unitRicciKernelProjection D
  have hπ := unitRicciKernelProjection_isLocalDiffeomorph D hc
  have hinv (p : UnitRicciKernel D) : (mfderiv (𝓡 n) (𝓡 n) proj p).IsInvertible :=
    ⟨hπ.mfderivToContinuousLinearEquiv (by simp) p, rfl⟩
  have hmetric (p : UnitRicciKernel D) (a b : TangentSpace (𝓡 n) p) :
      g'.inner p a b = g.inner (proj p)
        (mfderiv (𝓡 n) (𝓡 n) proj p a) (mfderiv (𝓡 n) (𝓡 n) proj p b) := rfl
  have hgeometry (p : UnitRicciKernel D) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) p ∧
        ∀ w : TangentSpace (𝓡 n) p, g'.leviCivitaData.connection X p w = 0 := by
    obtain ⟨U, V, hU, hp, hV, hVp, hn⟩ := hlocal p
    have hVs := hV.contMDiffAt (hU.mem_nhds hp)
    have hs : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (T% (mpullback (𝓡 n) (𝓡 n) proj V)) p :=
      hVs.mpullback_vectorField_preimage (f := proj) (hπ.contMDiff p) (hinv p) (by simp)
    have hgerm : X =ᶠ[𝓝 p] mpullback (𝓡 n) (𝓡 n) proj V := by
      filter_upwards [unitRicciKernel_eventually_eq_section D hU V hV
        (fun y _ => hdim y) (fun y hy => (hn y hy).1)
        (fun y hy => (hn y hy).2.1) p hp hVp] with q hq
      change (mfderiv (𝓡 n) (𝓡 n) proj q).inverse q.1.snd =
        (mfderiv (𝓡 n) (𝓡 n) proj q).inverse (V (proj q))
      rw [hq]
      rfl
    have hsm : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) p := by
      apply hs.congr_of_eventuallyEq
      filter_upwards [hgerm] with q hq
      exact congrArg (fun v : TangentSpace (𝓡 n) q =>
        (⟨q, v⟩ : TangentBundle (𝓡 n) (UnitRicciKernel D))) hq
    refine ⟨hsm, ?_⟩
    intro w
    have hd := g'.leviCivitaData.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hsm.mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp))
      (show (univ : Set (UnitRicciKernel D)) ∈ 𝓝 p from Filter.univ_mem) hgerm
    rw [congrArg (fun L => L w) hd,
      g'.leviCivitaData.connection_mpullback_of_metric_pullback D (hπ.contMDiff p)
        (Eventually.of_forall hinv) (Eventually.of_forall hmetric)
        (hVs.mdifferentiableAt (by simp)) w]
    exact (congrArg ((mfderiv (𝓡 n) (𝓡 n) proj p).inverse)
      ((hn _ hp).2.2 (mfderiv (𝓡 n) (𝓡 n) proj p w))).trans (map_zero _)
  refine ⟨fun p => (hgeometry p).1, ?_, fun p => (hgeometry p).2⟩
  intro p
  rw [hmetric, unitRicciKernelField_projection D hc p]
  exact p.2.1

end PoincareConjecture.M30
