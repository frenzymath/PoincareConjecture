import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Coordinate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.SmoothCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def unitRicciKernelCoordinate (D : LeviCivitaData g) (f : M → ℝ)
    (p : UnitRicciKernel D) : ℝ :=
  2 * g.inner p.1.proj (D.gradient f p.1.proj) p.1.snd

@[simp] theorem unitRicciKernelCoordinate_reverse (D : LeviCivitaData g)
    (f : M → ℝ) (p : UnitRicciKernel D) :
    unitRicciKernelCoordinate D f (unitRicciKernelReverse D p) =
      -unitRicciKernelCoordinate D f p := by
  simp [unitRicciKernelCoordinate, unitRicciKernelReverse]

theorem unitRicciKernel_eventually_eq_section (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (V : (y : M) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U)
    (hdim : ∀ y ∈ U, ricciNullity D y = 1)
    (hunit : ∀ y ∈ U, g.inner y (V y) (V y) = 1)
    (hnull : ∀ y ∈ U, ∀ w, D.ricci y (V y) w = 0)
    (p : UnitRicciKernel D) (hp : p.1.proj ∈ U) (hVp : V p.1.proj = p.1.snd) :
    ∀ᶠ q : UnitRicciKernel D in 𝓝 p, q.1.snd = V q.1.proj := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpcont := (continuous_unitRicciKernelProjection D).continuousAt (x := p)
  have hnear : ∀ᶠ q : UnitRicciKernel D in 𝓝 p, q.1.proj ∈ U :=
    hpcont.preimage_mem_nhds (hU.mem_nhds hp)
  have hs : ContinuousAt (fun q : UnitRicciKernel D =>
      (V q.1.proj : TangentBundle (𝓡 n) M)) p := by
    exact ContinuousAt.comp (f := unitRicciKernelProjection D)
      (hV.continuousOn.continuousAt (hU.mem_nhds hp)) hpcont
  have hi : ContinuousAt (fun q : UnitRicciKernel D =>
      g.inner q.1.proj q.1.snd (V q.1.proj)) p :=
    continuous_subtype_val.continuousAt.inner_bundle hs
  have hip : 0 < g.inner p.1.proj p.1.snd (V p.1.proj) := by
    rw [hVp, p.2.1]
    norm_num
  filter_upwards [hnear, hi.eventually (Ioi_mem_nhds hip)] with q hq hpos
  rcases unit_ricci_null_eq_or_eq_neg D q.1.proj (hdim _ hq)
      (V q.1.proj) q.1.snd (hnull _ hq) q.2.2 (hunit _ hq) q.2.1 with he | he
  · exact he
  · exfalso
    change 0 < g.inner q.1.proj q.1.snd (V q.1.proj) at hpos
    rw [he, map_neg, neg_apply, hunit _ hq] at hpos
    norm_num at hpos

theorem exists_local_parallel_unit_ricci_null_section_through
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1)
    (p : UnitRicciKernel (F.connection b)) :
    ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ p.1.proj ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧ V p.1.proj = p.1.snd ∧
      ∀ y ∈ U, (F.metric b).inner y (V y) (V y) = 1 ∧
        (∀ w, (F.connection b).ricci y (V y) w = 0) ∧
        ∀ w, (F.connection b).connection V y w = 0 := by
  obtain ⟨U, V, hU, hp, hV, hVp, hn⟩ := exists_local_smooth_unit_ricci_null_section
    (F.connection b) (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (Eventually.of_forall fun y => (hdim y).trans (hdim p.1.proj).symm)
    p.1.snd p.2.2 p.2.1
  refine ⟨U, V, hU, hp, hV, hVp, fun y hy => ⟨(hn y hy).1, (hn y hy).2, ?_⟩⟩
  intro v
  exact connection_eq_zero_of_terminal_unit_null hC hab F hsec V
    (hV.contMDiffAt (hU.mem_nhds hy))
    (Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => (hn z hz).2)
    (Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => (hn z hz).1) (hdim y) v

theorem unitRicciKernelCoordinate_local_geometry (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (V : (y : M) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U)
    (hdim : ∀ y ∈ U, ricciNullity D y = 1)
    (hunit : ∀ y ∈ U, g.inner y (V y) (V y) = 1)
    (hnull : ∀ y ∈ U, ∀ w, D.ricci y (V y) w = 0)
    (hparallel : ∀ y ∈ U, ∀ v, D.connection V y v = 0)
    (hsol : ∀ y ∈ U, ∀ v,
      D.hessian f y v (V y) = (1 / 2 : ℝ) * g.inner y v (V y))
    (p : UnitRicciKernel D) (hp : p.1.proj ∈ U) (hVp : V p.1.proj = p.1.snd) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let g' := unitRicciKernelMetric D hc
    let D' := g'.leviCivitaData
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (unitRicciKernelCoordinate D f) p ∧
      g'.inner p (D'.gradient (unitRicciKernelCoordinate D f) p)
        (D'.gradient (unitRicciKernelCoordinate D f) p) = 1 ∧
      ∀ v w, D'.hessian (unitRicciKernelCoordinate D f) p v w = 0 := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let g' := unitRicciKernelMetric D hc
  let D' := g'.leviCivitaData
  let proj := unitRicciKernelProjection D
  let c : M → ℝ := fun y => 2 * g.inner y (D.gradient f y) (V y)
  have hπ := unitRicciKernelProjection_isLocalDiffeomorph D hc
  have hcsm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ c (proj p) :=
    contMDiffAt_nullCoordinate D (hf.contMDiffAt (hU.mem_nhds hp))
      (hV.contMDiffAt (hU.mem_nhds hp))
  have heq : unitRicciKernelCoordinate D f =ᶠ[𝓝 p] c ∘ proj := by
    filter_upwards [unitRicciKernel_eventually_eq_section D hU V hV hdim hunit hnull
      p hp hVp] with q hq
    change 2 * g.inner q.1.proj (D.gradient f q.1.proj) q.1.snd =
      2 * g.inner q.1.proj (D.gradient f q.1.proj) (V q.1.proj)
    rw [hq]
  have hinv (q : UnitRicciKernel D) : (mfderiv (𝓡 n) (𝓡 n) proj q).IsInvertible :=
    ⟨hπ.mfderivToContinuousLinearEquiv (by simp) q, rfl⟩
  have hmetric (q : UnitRicciKernel D) (v w : TangentSpace (𝓡 n) q) :
      g'.inner q v w = g.inner (proj q)
        (mfderiv (𝓡 n) (𝓡 n) proj q v) (mfderiv (𝓡 n) (𝓡 n) proj q w) := rfl
  have hgrad : D'.gradient (unitRicciKernelCoordinate D f) p =
      (mfderiv (𝓡 n) (𝓡 n) proj p).inverse p.1.snd := by
    have hgerm : D'.gradient (unitRicciKernelCoordinate D f) p =
        D'.gradient (c ∘ proj) p := by
      unfold LeviCivitaData.gradient
      rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
    rw [hgerm, D'.gradient_comp_eq_mpullback D
      ((hπ p).mdifferentiableAt (by simp)) (hcsm.mdifferentiableAt (by simp))
      (hinv p) (hmetric p)]
    change (mfderiv (𝓡 n) (𝓡 n) proj p).inverse (D.gradient c (proj p)) = _
    exact congrArg ((mfderiv (𝓡 n) (𝓡 n) proj p).inverse)
      ((gradient_nullCoordinate D (hf.contMDiffAt (hU.mem_nhds hp))
        (hV.contMDiffAt (hU.mem_nhds hp)) (hparallel _ hp) (hsol _ hp)).trans hVp)
  refine ⟨(hcsm.comp p (hπ.contMDiff p)).congr_of_eventuallyEq heq, ?_, ?_⟩
  · rw [hgrad, hmetric, (hinv p).self_apply_inverse]
    exact p.2.1
  · intro v w
    rw [D'.hessian_eq_of_eventuallyEq heq,
      D'.hessian_comp_of_metric_pullback D (hπ.contMDiff p)
        (Eventually.of_forall hinv) (Eventually.of_forall hmetric) hcsm]
    exact hessian_nullCoordinate D hU hf hV hparallel hsol hp _ _

theorem unitRicciKernelCoordinate_geometry_of_terminal_soliton
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hsol : ∀ y, ∀ v w, (F.connection b).ricci y v w +
      (F.connection b).hessian f y v w = (1 / 2 : ℝ) * (F.metric b).inner y v w) :
    let hc := unitRicciKernel_isCoveringMap_of_terminal_nullity_one hC hab F hsec hdim
    letI := unitRicciKernelChartedSpace (F.connection b) hc
    letI := unitRicciKernelIsManifold (F.connection b) hc
    let D' := (unitRicciKernelMetric (F.connection b) hc).leviCivitaData
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (unitRicciKernelCoordinate (F.connection b) f) ∧
      RiemannianMetric.HasUnitGradient D' (unitRicciKernelCoordinate (F.connection b) f) ∧
      RiemannianMetric.HasZeroHessian D' (unitRicciKernelCoordinate (F.connection b) f) := by
  let hc := unitRicciKernel_isCoveringMap_of_terminal_nullity_one hC hab F hsec hdim
  let := unitRicciKernelChartedSpace (F.connection b) hc
  let := unitRicciKernelIsManifold (F.connection b) hc
  let D' := (unitRicciKernelMetric (F.connection b) hc).leviCivitaData
  have hlocal (p : UnitRicciKernel (F.connection b)) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (unitRicciKernelCoordinate (F.connection b) f) p ∧
        (unitRicciKernelMetric (F.connection b) hc).inner p
          (D'.gradient (unitRicciKernelCoordinate (F.connection b) f) p)
          (D'.gradient (unitRicciKernelCoordinate (F.connection b) f) p) = 1 ∧
        ∀ v w, D'.hessian (unitRicciKernelCoordinate (F.connection b) f) p v w = 0 := by
    obtain ⟨U, V, hU, hp, hV, hVp, hn⟩ :=
      exists_local_parallel_unit_ricci_null_section_through hC hab F hsec hdim p
    have hs (y : M) (hy : y ∈ U) (v : TangentSpace (𝓡 n) y) :
        (F.connection b).hessian f y v (V y) =
          (1 / 2 : ℝ) * (F.metric b).inner y v (V y) := by
      have he := hsol y v (V y)
      have hsym := ((hC.tensor_calculus n M (F.metric b) (F.connection b)).2.2.2.1
        y v (V y) v (V y)).2.2.2
      rw [hsym, (hn y hy).2.1 v, zero_add] at he
      exact he
    exact unitRicciKernelCoordinate_local_geometry (F.connection b) hc hU hf.contMDiffOn
      V hV (fun y _ => hdim y) (fun y hy => (hn y hy).1)
      (fun y hy => (hn y hy).2.1) (fun y hy => (hn y hy).2.2) hs p hp hVp
  exact ⟨fun p => (hlocal p).1, fun p => (hlocal p).2.1, fun p => (hlocal p).2.2⟩

end PoincareConjecture.RicciFlow.Splitting
