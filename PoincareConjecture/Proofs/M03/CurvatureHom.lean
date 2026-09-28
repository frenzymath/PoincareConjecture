import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import PoincareConjecture.Proofs.M03.CurvatureJoint
import PoincareConjecture.Proofs.M03.FamilyTangentTimeDerivative
import PoincareConjecture.Proofs.M03.MetricInverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Multilinear.Curry









set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_curvature_continuousTrilinearMap {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) :
    ∃ R : TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      ∀ u v w, R u v w = D.curvature x u v w := by
  have : T2Space (TangentSpace (𝓡 n) x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  obtain ⟨L, hL⟩ := exists_curvature_trilinearMap D x
  let e₁ : (TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x) ≃ₗ[ℝ]
      (TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) :=
    LinearMap.toContinuousLinearMap
  let e₂ : (TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x) ≃ₗ[ℝ]
      (TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) :=
    ((LinearEquiv.refl ℝ (TangentSpace (𝓡 n) x)).arrowCongr e₁).trans
      LinearMap.toContinuousLinearMap
  refine ⟨(e₂.toLinearMap.comp L).toContinuousLinearMap, ?_⟩
  intro u v w
  exact hL u v w

theorem exists_contMDiffOn_curvature_family_trilinearMap
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t)) :
    letI : NormedAddCommGroup
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
    letI : NormedSpace ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
    letI : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
    letI : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
    ∃ R : (t : ℝ) → (x : M) → TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      (∀ t x u v w, R t x u v w = (D t).curvature x u v w) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M => Bundle.TotalSpace.mk'
          (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (E := fun x : M => TangentSpace (𝓡 n) x →L[ℝ]
            TangentSpace (𝓡 n) x →L[ℝ]
            TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
          p.2 (R p.1 p.2)) (J ×ˢ Set.univ) := by
  classical
  let : NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
  let : NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
  let : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := inferInstance
  choose R hR using fun t x => exists_curvature_continuousTrilinearMap (D t) x
  refine ⟨R, hR, ?_⟩
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2
  have hep : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
  let frame (a : EuclideanSpace ℝ (Fin n)) (x : M) : TangentSpace (𝓡 n) x :=
    e.symmL ℝ x a
  have hframe (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro x hx
    simpa [frame, Trivialization.symmL_apply _ hx] using
      congrArg Prod.snd (e.apply_mk_symm hx a)
  let C (q : ℝ × M) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (fun x => TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
      p.2 q.2 p.2 q.2 (R q.1 q.2)
  have hbase : ∀ᶠ q in 𝓝[J ×ˢ (Set.univ : Set M)] p, q.2 ∈ e.baseSet :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_snd.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hep))
  have hsmall : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ (Set.univ : Set M)] p := by
    filter_upwards [self_mem_nhdsWithin, hbase] with q hq hqe
    exact ⟨hq.1, hqe⟩
  have hC : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      C (J ×ˢ Set.univ) p := by
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro a
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro b
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro c
    have hs := contMDiffOn_family_curvature hg D e.open_baseSet
      (frame a) (frame b) (frame c) (hframe a) (hframe b) (hframe c)
    have hc := (Bundle.contMDiffWithinAt_totalSpace.mp
      ((hs p ⟨hp.1, hep⟩).mono_of_mem_nhdsWithin hsmall)).2
    apply hc.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hbase] with q hq
    have hqh : q.2 ∈ (trivializationAt
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) p.2).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hq, hq⟩
    dsimp [C]
    rw [inCoordinates_apply_eq₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
      (F₃ := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
      hq hq hqh]
    rw [← Trivialization.symmL_apply (R := ℝ) e hq a,
      ← Trivialization.symmL_apply (R := ℝ) e hq b]
    rw [Trivialization.linearMapAt_apply, if_pos hqh, hom_trivializationAt_apply]
    change e.linearMapAt ℝ q.2
      (R q.1 q.2 (frame a q.2) (frame b q.2) (frame c q.2)) = _
    rw [hR, Trivialization.linearMapAt_apply, if_pos hq]
  let F : ℝ × M → TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (fun x => TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) :=
    fun q => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) q.2 (R q.1 q.2)
  exact (contMDiffWithinAt_hom_bundle F (s := J ×ˢ Set.univ) (x₀ := p)).mpr
    ⟨contMDiffWithinAt_snd, hC⟩

theorem hasDerivAt_ricciFlow_iteratedCurvature_moving_inputs
    {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X : Fin (k + 3) → ℝ → (y : M) → TangentSpace (𝓡 n) y)
    (hX : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (X j p.1 p.2)) (J ×ˢ U))
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    HasDerivAt
      (fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k (fun j => X j s) x)
      (deriv (fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
        (fun j => X j t) x) t +
      ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative (F.connection t) k
        (Function.update (fun i => X i t) j (fun y => deriv (fun s => X j s y) t)) x) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) ℝ) := inferInstance
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) ℝ) := inferInstance
  let : NormedAddCommGroup (ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x)) := inferInstance
  let : NormedSpace ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x)) := inferInstance
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
  let dotX := fun (j : Fin (k + 3)) (y : M) => deriv (fun s => X j s y) t
  let S := fun V : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U
  have htJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hXs (j : Fin (k + 3)) (s : ℝ) (hs : s ∈ J) : S (X j s) :=
    (hX j).comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hy => ⟨hs, hy⟩)
  have hdot (j : Fin (k + 3)) :
      (∀ y ∈ U, HasDerivAt (fun s => X j s y) (dotX j y) t) ∧ S (dotX j) :=
    family_tangent_time_derivative (F.metric 0) hU (X j) (hX j) ht
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let b := e.basisAt b0 he
  let E := e.localFrame b0
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i
  have hEx (i : Fin n) : E i x = b i := e.localFrame_apply_of_mem_baseSet b0 he
  let c (a : Fin (k + 3) → Fin n) :
      ContinuousMultilinearMap ℝ (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) ℝ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin (k + 3)) ℝ).compContinuousLinearMap
      (fun j => (b.coord (a j)).toContinuousLinearMap)
  have hc (a : Fin (k + 3) → Fin n) (v : Fin (k + 3) → TangentSpace (𝓡 n) x) :
      c a v = ∏ j, b.repr (v j) (a j) := by
    simp only [c, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
  let T : ℝ → ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x) := fun s =>
    ∑ a : Fin (k + 3) → Fin n, (c a).smulRight (K s (fun j => E (a j)) x)
  have heval (s : ℝ) (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) : T s (fun j => V j x) = K s V x := by
    obtain ⟨L, hL⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap
      (F.connection s) k x
    have hcoeff (a : Fin (k + 3) → Fin n) :
        L (fun j => b (a j)) = K s (fun j => E (a j)) x := by
      simpa only [hEx] using hL e.open_baseSet (fun j => E (a j)) (fun j => hE (a j)) he
    calc
      T s (fun j => V j x) = ∑ a : Fin (k + 3) → Fin n,
          (∏ j, b.repr (V j x) (a j)) • L (fun j => b (a j)) := by
        simp only [T, sum_apply, ContinuousMultilinearMap.smulRight_apply, hc, hcoeff]
      _ = L (fun j => V j x) := by
        have hh := L.map_sum (fun (j : Fin (k + 3)) (i : Fin n) => b.repr (V j x) i • b i)
        simp only [L.map_smul_univ] at hh
        have hrec : (fun j => ∑ i : Fin n, b.repr (V j x) i • b i) = (fun j => V j x) :=
          funext (fun j => b.sum_repr (V j x))
        rw [hrec] at hh
        exact hh.symm
      _ = K s V x := hL hU V hV hx
  have hcoef (a : Fin (k + 3) → Fin n) :
      HasDerivAt (fun s => K s (fun j => E (a j)) x)
        (deriv (fun s => K s (fun j => E (a j)) x) t) t := by
    have hfamily := contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun j _ => E (a j))
      (fun j => (hE (a j)).comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun _ hp => hp.2))
    exact (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s => K s (fun j => E (a j))) hfamily ht).1 x he
  let Tdot : ContinuousMultilinearMap ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x) :=
    ∑ a : Fin (k + 3) → Fin n, (c a).smulRight
      (deriv (fun s => K s (fun j => E (a j)) x) t)
  have hTd : HasDerivAt T Tdot t := by
    apply HasDerivAt.fun_sum
    intro a _
    exact ((ContinuousMultilinearMap.smulRightL ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x) (c a)).hasFDerivAt).comp_hasDerivAt
        t (hcoef a)
  have hfrozen : HasDerivAt (fun s => K s (fun j => X j t) x)
      (Tdot (fun j => X j t x)) t := by
    have hh := (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x) (TangentSpace (𝓡 n) x)
      (fun j => X j t x)).hasFDerivAt.comp_hasDerivAt t hTd
    apply hh.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s =>
      (heval s (fun j => X j t) (fun j => hXs j t (interior_subset ht))).symm)
  have hmoving : HasDerivAt (fun s => T s (fun j => X j s x))
      (Tdot (fun j => X j t x) +
        ∑ j, T t (Function.update (fun i => X i t x) j (dotX j x))) t := by
    have hh := (hTd.hasFDerivAt.continuousMultilinearMap_apply
      (fun j => ((hdot j).1 x hx).hasFDerivAt)).hasDerivAt
    simpa using hh
  have hslot (j : Fin (k + 3)) :
      T t (Function.update (fun i => X i t x) j (dotX j x)) =
        K t (Function.update (fun i => X i t) j (dotX j)) x := by
    have hV : ∀ i, S (Function.update (fun i => X i t) j (dotX j) i) := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [Function.update_self] using (hdot j).2
      · simpa only [Function.update_of_ne hij] using hXs i t (interior_subset ht)
    have hh := heval t (Function.update (fun i => X i t) j (dotX j)) hV
    convert hh using 1
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hij]
  have hcurve : (fun s => K s (fun j => X j s) x) =ᶠ[𝓝 t]
      (fun s => T s (fun j => X j s x)) := by
    filter_upwards [htJ] with s hs
    exact (heval s (fun j => X j s) (fun j => hXs j s hs)).symm
  have hh := hmoving.congr_of_eventuallyEq hcurve
  rw [← hfrozen.deriv] at hh
  simpa only [hslot] using hh

set_option maxHeartbeats 2400000 in

theorem curvature_iterated_squared_norm_frame_eq_orthonormal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let K := curvatureOnFields_iteratedCovariantDerivative D k
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend V (b i)
    let kf := fun α : Fin (k + 3) → Fin n => K (fun r => E (α r)) x
    let kb := fun γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    (∑ α, ∑ β, (∏ r, a (α r) (β r)) * g.inner x (kf α) (kf β)) =
      ∑ γ, g.inner x (kb γ) (kb γ) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let K := curvatureOnFields_iteratedCovariantDerivative D k
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let kf := fun α : Fin (k + 3) → Fin n => K (fun r => E (α r)) x
  let kb := fun γ : Fin (k + 3) → ι => K (fun r => ext (γ r)) x
  change (∑ α, ∑ β, (∏ r, a (α r) (β r)) * g.inner x (kf α) (kf β)) =
    ∑ γ, g.inner x (kb γ) (kb γ)
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D k x
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hET (α : Fin (k + 3) → Fin n) : T (fun r => E (α r) x) = kf α :=
    hT e.open_baseSet (fun r => E (α r)) (fun r => hE (α r)) hx
  let e0 := trivializationAt V (TangentSpace (𝓡 n)) x
  have hx0 : x ∈ e0.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (i : ι) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext i)) e0.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e0 ⟨x, b i⟩).2) e0.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e0 ⟨y, ext i y⟩).2) e0.baseSet := by
      apply hc.congr
      intro y hy
      change (e0 ⟨y, e0.symm y (e0 ⟨x, b i⟩).2⟩).2 = (e0 ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (e0.apply_mk_symm hy (e0 ⟨x, b i⟩).2)
    intro y hy
    rw [e0.contMDiffWithinAt_section _ hy]
    exact hec y hy
  have hBT (γ : Fin (k + 3) → ι) : T (fun r => b (γ r)) = kb γ := by
    simpa only [ext, FiberBundle.extend_apply_self] using
      hT e0.open_baseSet (fun r => ext (γ r)) (fun r => hExt (γ r)) hx0
  have hrec (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have hExpand (γ : Fin (k + 3) → ι) : kb γ =
      ∑ α : Fin (k + 3) → Fin n, (∏ r, theta (α r) x (b (γ r))) • kf α := by
    calc
      _ = T (fun r => b (γ r)) := (hBT γ).symm
      _ = T (fun r => ∑ i : Fin n, theta i x (b (γ r)) • E i x) :=
        congrArg T (funext fun r => hrec (b (γ r)))
      _ = ∑ α : Fin (k + 3) → Fin n,
          T (fun r => theta (α r) x (b (γ r)) • E (α r) x) :=
        T.map_sum (fun r i => theta i x (b (γ r)) • E i x)
      _ = _ := by simp only [MultilinearMap.map_smul_univ, hET]
  have htrace (i j : Fin n) : a i j =
      ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  calc
    _ = ∑ γ : Fin (k + 3) → ι,
        g.inner x (∑ α, (∏ r, theta (α r) x (b (γ r))) • kf α)
          (∑ β, (∏ r, theta (β r) x (b (γ r))) • kf β) :=
      curvature_all_rank_gram_contraction (g.inner x) a (fun p i => theta i x (b p))
        htrace kf kf
    _ = _ := by simp only [← hExpand]

set_option maxHeartbeats 2400000 in

theorem curvature_iterated_tangentNorm_le_orthonormal_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ)
    {U : Set M} (hU : IsOpen U)
    (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hX : ∀ r, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X r)) U)
    {x : M} (hx : x ∈ U) :
    let K := curvatureOnFields_iteratedCovariantDerivative D k
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    g.tangentNorm x (K X x) ≤ Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) *
      ∏ r, g.tangentNorm x (X r x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let K := curvatureOnFields_iteratedCovariantDerivative D k
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let kb := fun γ : Fin (k + 3) → ι => K (fun r => ext (γ r)) x
  let q := ∑ γ : Fin (k + 3) → ι, g.inner x (kb γ) (kb γ)
  have hpair (z : TangentSpace (𝓡 n) x) : g.inner x z z = ‖z‖ ^ 2 :=
    real_inner_self_eq_norm_sq z
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm, hpair, Real.sqrt_sq (norm_nonneg _)]
  change g.tangentNorm x (K X x) ≤ Real.sqrt q * ∏ r, g.tangentNorm x (X r x)
  simp only [hnorm]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D k x
  let v : Fin (k + 3) → TangentSpace (𝓡 n) x := fun r => X r x
  have hTv : T v = K X x := hT hU X hX hx
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (i : ι) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext i)) e.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e ⟨x, b i⟩).2) e.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e ⟨y, ext i y⟩).2) e.baseSet := by
      apply hc.congr
      intro y hy
      change (e ⟨y, e.symm y (e ⟨x, b i⟩).2⟩).2 = (e ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (e.apply_mk_symm hy (e ⟨x, b i⟩).2)
    intro y hy
    rw [e.contMDiffWithinAt_section _ hy]
    exact hec y hy
  let tb := fun γ : Fin (k + 3) → ι => T (fun r => b (γ r))
  have htb (γ : Fin (k + 3) → ι) : tb γ = kb γ := by
    simpa only [ext, FiberBundle.extend_apply_self] using
      hT e.open_baseSet (fun r => ext (γ r)) (fun r => hExt (γ r)) hxe
  let c := fun γ : Fin (k + 3) → ι => ∏ r, b.repr (v r) (γ r)
  have hExpand : T v = ∑ γ : Fin (k + 3) → ι, c γ • tb γ := by
    calc
      _ = T (fun r => ∑ i : ι, b.repr (v r) i • b i) :=
        congrArg T (funext fun r => (b.sum_repr (v r)).symm)
      _ = ∑ γ : Fin (k + 3) → ι, T (fun r => b.repr (v r) (γ r) • b (γ r)) :=
        T.map_sum (fun r i => b.repr (v r) i • b i)
      _ = _ := by simp only [MultilinearMap.map_smul_univ, c, tb]
  let H := ∏ r : Fin (k + 3), ‖v r‖
  have hrepr (z : TangentSpace (𝓡 n) x) :
      ∑ i : ι, b.repr z i ^ 2 = ‖z‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right z
  have hweight : (∑ γ : Fin (k + 3) → ι, |c γ| ^ 2) = H ^ 2 := by
    calc
      _ = ∑ γ : Fin (k + 3) → ι, ∏ r, b.repr (v r) (γ r) ^ 2 := by
        simp only [c, sq_abs, Finset.prod_pow]
      _ = ∏ r : Fin (k + 3), ∑ i : ι, b.repr (v r) i ^ 2 :=
        (Fintype.prod_sum (fun r i => b.repr (v r) i ^ 2)).symm
      _ = ∏ r : Fin (k + 3), ‖v r‖ ^ 2 := by simp only [hrepr]
      _ = H ^ 2 := by dsimp only [H]; rw [Finset.prod_pow]
  have hq : q = ∑ γ : Fin (k + 3) → ι, ‖tb γ‖ ^ 2 := by
    simp only [q, htb, hpair]
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  let S := ∑ γ : Fin (k + 3) → ι, |c γ| * ‖tb γ‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (k + 3) → ι))
    (fun γ => |c γ|) (fun γ => ‖tb γ‖)
  change S ^ 2 ≤ _ at hcs
  rw [hweight, ← hq] at hcs
  have hbound : S ≤ Real.sqrt q * H := by
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hright : 0 ≤ Real.sqrt q * H := by dsimp only [H]; positivity
    have hsquare : S ^ 2 ≤ (Real.sqrt q * H) ^ 2 := by
      calc
        _ ≤ H ^ 2 * q := hcs
        _ = _ := by rw [mul_pow (Real.sqrt q) H 2, Real.sq_sqrt hq0]; ring
    exact (sq_le_sq₀ hS0 hright).mp hsquare
  calc
    ‖K X x‖ = ‖T v‖ := congrArg norm hTv.symm
    _ = ‖∑ γ : Fin (k + 3) → ι, c γ • tb γ‖ := congrArg norm hExpand
    _ ≤ ∑ γ : Fin (k + 3) → ι, ‖c γ • tb γ‖ := norm_sum_le _ _
    _ = S := by simp only [S, norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt q * H := hbound


theorem abs_curvature_iterated_pairing_le_orthonormal_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ)
    {U : Set M} (hU : IsOpen U)
    (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hX : ∀ r, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X r)) U)
    {x : M} (hx : x ∈ U) (w : TangentSpace (𝓡 n) x) :
    let K := curvatureOnFields_iteratedCovariantDerivative D k
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    |g.inner x (K X x) w| ≤ Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) *
      (∏ r, g.tangentNorm x (X r x)) * g.tangentNorm x w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm, show g.inner x z z = ‖z‖ ^ 2 from
      real_inner_self_eq_norm_sq z, Real.sqrt_sq (norm_nonneg _)]
  have hpair (z : TangentSpace (𝓡 n) x) :
      |g.inner x z w| ≤ g.tangentNorm x z * g.tangentNorm x w := by
    rw [hnorm, hnorm]
    exact abs_real_inner_le_norm z w
  have hvec := curvature_iterated_tangentNorm_le_orthonormal_energy D k hU X hX hx
  dsimp only at hvec ⊢
  exact (hpair _).trans (mul_le_mul_of_nonneg_right hvec (Real.sqrt_nonneg _))


theorem multilinear_two_trace_frame_eq_orthonormal
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x0 x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (T : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let b := g.orthonormalBasis x
    (∑ γ : Fin 4 → Fin n,
      a (γ 0) (γ 1) * a (γ 2) (γ 3) * T (fun r => E (γ r) x)) =
      ∑ p, ∑ q, T ![b p, b p, b q, b q] := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let c := fun (p : ι) (i : Fin n) => theta i x (b p)
  let f := fun γ : Fin 4 → Fin n => T (fun r => E (γ r) x)
  change (∑ γ : Fin 4 → Fin n, a (γ 0) (γ 1) * a (γ 2) (γ 3) * f γ) =
    ∑ p : ι, ∑ q : ι, T ![b p, b p, b q, b q]
  have hrec (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have htrace (i j : Fin n) : a i j = ∑ p : ι, c p i * c p j :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hexpand (p q : ι) : T ![b p, b p, b q, b q] =
      ∑ γ : Fin 4 → Fin n,
        (c p (γ 0) * c p (γ 1) * c q (γ 2) * c q (γ 3)) * f γ := by
    let Z : Fin 4 → TangentSpace (𝓡 n) x := ![b p, b p, b q, b q]
    change T Z = _
    calc
      T Z = T (fun r => ∑ i : Fin n, theta i x (Z r) • E i x) :=
        congrArg T (funext fun r => hrec (Z r))
      _ = ∑ γ : Fin 4 → Fin n,
          T (fun r => theta (γ r) x (Z r) • E (γ r) x) :=
        T.map_sum (fun (r : Fin 4) (i : Fin n) => theta i x (Z r) • E i x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [MultilinearMap.map_smul_univ, Fin.prod_univ_four]
        rfl
  symm
  calc
    _ = ∑ p : ι, ∑ q : ι, ∑ γ : Fin 4 → Fin n,
        (c p (γ 0) * c p (γ 1) * c q (γ 2) * c q (γ 3)) * f γ := by
      simp_rw [hexpand]
    _ = ∑ p : ι, ∑ γ : Fin 4 → Fin n, ∑ q : ι,
        (c p (γ 0) * c p (γ 1) * c q (γ 2) * c q (γ 3)) * f γ := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = ∑ γ : Fin 4 → Fin n, ∑ p : ι, ∑ q : ι,
        (c p (γ 0) * c p (γ 1) * c q (γ 2) * c q (γ 3)) * f γ :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [htrace, htrace]
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem abs_curvature_two_factor_contraction_le_orthonormal_energy
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p q : ℕ)
    {σ : Type v} [Fintype σ]
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (σ ⊕ Fin 4)) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := curvatureOnFields_iteratedCovariantDerivative D
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    let fill := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y)
      (γ : Fin 4 → Fin n) s => Sum.elim X (fun j => E (γ j)) (slots s)
    let Q := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y) y =>
      ∑ γ : Fin 4 → Fin n, (a y (γ 0) (γ 1) * a y (γ 2) (γ 3)) *
        (low p (fun j => fill X γ (Sum.inl j)) y *
          low q (fun j => fill X γ (Sum.inr j)) y)
    ∀ (X : σ → (y : M) → TangentSpace (𝓡 n) y),
      (∀ s, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X s)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      (∀ s, g.tangentNorm x (X s x) ≤ 1) →
      let b := g.orthonormalBasis x
      let ext := fun i => FiberBundle.extend V (b i)
      let ell := fun r =>
        Real.sqrt (∑ γ : Fin (r + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          g.inner x (K r (fun j => ext (γ j)) x) (K r (fun j => ext (γ j)) x))
      |Q X x| ≤ (n : ℝ) ^ 2 * ell p * ell q := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let fill := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y)
    (γ : Fin 4 → Fin n) s => Sum.elim X (fun j => E (γ j)) (slots s)
  let Q := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ γ : Fin 4 → Fin n, (a y (γ 0) (γ 1) * a y (γ 2) (γ 3)) *
      (low p (fun j => fill X γ (Sum.inl j)) y *
        low q (fun j => fill X γ (Sum.inr j)) y)
  intro X hX x hx hunit
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let ext := fun i : ι => FiberBundle.extend V (b i)
  let ell := fun r =>
    Real.sqrt (∑ γ : Fin (r + 3) → ι,
      g.inner x (K r (fun j => ext (γ j)) x) (K r (fun j => ext (γ j)) x))
  change |Q X x| ≤ (n : ℝ) ^ 2 * ell p * ell q
  let T := fun r => Classical.choose
    (exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D r x)
  have hT (r : ℕ) {U : Set M} (hU : IsOpen U)
      (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Z j)) U)
      (hxU : x ∈ U) : T r (fun j => Z j x) = K r Z x :=
    Classical.choose_spec
      (exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D r x) hU Z hZ hxU
  let L : (r : ℕ) → MultilinearMap ℝ
      (fun _ : Fin (r + 4) => TangentSpace (𝓡 n) x) ℝ := fun r => MultilinearMap.mk'
    (fun z : Fin (r + 4) → TangentSpace (𝓡 n) x =>
      g.inner x (T r (Fin.init z)) (z (Fin.last (r + 3))))
    (by
      intro z j u v
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.init_update_last, Function.update_self, map_add]
      · simp only [Fin.init_update_castSucc,
          Function.update_of_ne (Fin.castSucc_ne_last i).symm,
          (T r).map_update_add, map_add, add_apply])
    (by
      intro z j c u
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.init_update_last, Function.update_self, map_smul]
      · simp only [Fin.init_update_castSucc,
          Function.update_of_ne (Fin.castSucc_ne_last i).symm,
          (T r).map_update_smul, map_smul, smul_apply])
  have hL (r : ℕ) {U : Set M} (hU : IsOpen U)
      (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Z j)) U)
      (hxU : x ∈ U) : L r (fun j => Z j x) = low r Z x := by
    change g.inner x (T r (fun j => Fin.init Z j x)) (Z (Fin.last (r + 3)) x) = _
    rw [hT r hU (Fin.init Z) (fun j => hZ j.castSucc) hxU]
  let A : MultilinearMap ℝ
      (fun _ : Fin (p + 4) ⊕ Fin (q + 4) => TangentSpace (𝓡 n) x) ℝ :=
    ((L p).smulRight (L q)).uncurrySum
  let W : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ :=
    (A.domDomCongr slots).currySum (fun s => X s x)
  have hW (z : Fin 4 → TangentSpace (𝓡 n) x) :
      W z =
        L p (fun j => Sum.elim (fun s => X s x) z (slots (Sum.inl j))) *
          L q (fun j => Sum.elim (fun s => X s x) z (slots (Sum.inr j))) := rfl
  have hWfields {U : Set M} (hU : IsOpen U)
      (Y : Fin 4 → (y : M) → TangentSpace (𝓡 n) y)
      (hXU : ∀ s, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X s)) U)
      (hY : ∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Y j)) U)
      (hxU : x ∈ U) :
      W (fun j => Y j x) =
        low p (fun j => Sum.elim X Y (slots (Sum.inl j))) x *
          low q (fun j => Sum.elim X Y (slots (Sum.inr j))) x := by
    have hval (s : σ ⊕ Fin 4) :
        Sum.elim (fun s => X s x) (fun j => Y j x) s = Sum.elim X Y s x := by
      cases s <;> rfl
    have hXY (s : σ ⊕ Fin 4) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Sum.elim X Y s)) U := by
      cases s with
      | inl s => exact hXU s
      | inr j => exact hY j
    rw [hW]
    simp only [hval]
    rw [hL p hU _ (fun j => hXY _) hxU, hL q hU _ (fun j => hXY _) hxU]
  have hE (i : Fin n) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hQ : Q X x = ∑ γ : Fin 4 → Fin n,
      (a x (γ 0) (γ 1) * a x (γ 2) (γ 3)) * W (fun r => E (γ r) x) := by
    apply Finset.sum_congr rfl
    intro γ _
    rw [hWfields e.open_baseSet (fun r => E (γ r)) hX (fun r => hE _) hx]
  have htrace := multilinear_two_trace_frame_eq_orthonormal g x0 x hx W
  change (∑ γ : Fin 4 → Fin n,
      (a x (γ 0) (γ 1) * a x (γ 2) (γ 3)) * W (fun r => E (γ r) x)) =
    ∑ i : ι, ∑ j : ι, W ![b i, b i, b j, b j] at htrace
  have hnonneg (z : TangentSpace (𝓡 n) x) : 0 ≤ g.tangentNorm x z :=
    Real.sqrt_nonneg _
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm,
      show g.inner x z z = ‖z‖ ^ 2 from real_inner_self_eq_norm_sq z,
      Real.sqrt_sq (norm_nonneg _)]
  have hlowUnit (r : ℕ) {U : Set M} (hU : IsOpen U)
      (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Z j)) U)
      (hxU : x ∈ U) (hZunit : ∀ j, g.tangentNorm x (Z j x) ≤ 1) :
      |low r Z x| ≤ ell r := by
    have hh := abs_curvature_iterated_pairing_le_orthonormal_energy D r hU
      (Fin.init Z) (fun j => hZ j.castSucc) hxU (Z (Fin.last (r + 3)) x)
    change |low r Z x| ≤ ell r * (∏ j : Fin (r + 3),
      g.tangentNorm x (Z j.castSucc x)) * g.tangentNorm x (Z (Fin.last (r + 3)) x) at hh
    have hp : (∏ j : Fin (r + 3), g.tangentNorm x (Z j.castSucc x)) ≤ 1 :=
      Finset.prod_le_one (fun j _ => hnonneg _) (fun j _ => hZunit j.castSucc)
    have hall : (∏ j : Fin (r + 3), g.tangentNorm x (Z j.castSucc x)) *
        g.tangentNorm x (Z (Fin.last (r + 3)) x) ≤ 1 := by
      simpa only [one_mul] using
        mul_le_mul hp (hZunit (Fin.last (r + 3))) (hnonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
    calc
      _ ≤ ell r * (∏ j : Fin (r + 3), g.tangentNorm x (Z j.castSucc x)) *
          g.tangentNorm x (Z (Fin.last (r + 3)) x) := hh
      _ = ell r * ((∏ j : Fin (r + 3), g.tangentNorm x (Z j.castSucc x)) *
          g.tangentNorm x (Z (Fin.last (r + 3)) x)) := mul_assoc _ _ _
      _ ≤ ell r * 1 := mul_le_mul_of_nonneg_left hall (Real.sqrt_nonneg _)
      _ = ell r := mul_one _
  let ex := trivializationAt V (TangentSpace (𝓡 n)) x
  have hxx : x ∈ ex.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (i : ι) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext i)) ex.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (ex ⟨x, b i⟩).2) ex.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (ex ⟨y, ext i y⟩).2) ex.baseSet := by
      apply hc.congr
      intro y hy
      change (ex ⟨y, ex.symm y (ex ⟨x, b i⟩).2⟩).2 = (ex ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (ex.apply_mk_symm hy (ex ⟨x, b i⟩).2)
    intro y hy
    rw [ex.contMDiffWithinAt_section _ hy]
    exact hec y hy
  let U := e.baseSet ∩ ex.baseSet
  have hU : IsOpen U := e.open_baseSet.inter ex.open_baseSet
  have hxU : x ∈ U := ⟨hx, hxx⟩
  have hterm (i j : ι) : |W ![b i, b i, b j, b j]| ≤ ell p * ell q := by
    let Y := fun r : Fin 4 => ext (![i, i, j, j] r)
    have hY : ∀ r, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Y r)) U :=
      fun r => (hExt _).mono inter_subset_right
    have hXY (s : σ ⊕ Fin 4) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Sum.elim X Y s)) U := by
      cases s with
      | inl s => exact (hX s).mono inter_subset_left
      | inr r => exact hY r
    have hXYunit (s : σ ⊕ Fin 4) : g.tangentNorm x (Sum.elim X Y s x) ≤ 1 := by
      cases s with
      | inl s => exact hunit s
      | inr r =>
        simp only [Sum.elim_inr, Y, ext, FiberBundle.extend_apply_self, hnorm]
        exact (b.norm_eq_one _).le
    have hYx : (fun r => Y r x) = ![b i, b i, b j, b j] := by
      funext r
      fin_cases r <;> simp [Y, ext]
    rw [← hYx, hWfields hU Y (fun s => (hX s).mono inter_subset_left) hY hxU, abs_mul]
    exact mul_le_mul
      (hlowUnit p hU _ (fun r => hXY _) hxU (fun r => hXYunit _))
      (hlowUnit q hU _ (fun r => hXY _) hxU (fun r => hXYunit _))
      (abs_nonneg _) (Real.sqrt_nonneg _)
  have hdim : Fintype.card ι = n := by
    dsimp only [ι]
    rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) x,
      finrank_euclideanSpace_fin]
  rw [hQ, htrace]
  calc
    _ ≤ ∑ i : ι, |∑ j : ι, W ![b i, b i, b j, b j]| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ∑ j : ι, |W ![b i, b i, b j, b j]| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ell p * ell q :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (n : ℝ) ^ 2 * ell p * ell q := by
      simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul]
      ring


theorem curvature_iterated_orthonormal_energy_nonneg_and_eq_sq_sqrt
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ) (x : M) :
    let K := curvatureOnFields_iteratedCovariantDerivative D k
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun γ : Fin (k + 3) →
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    let Q := ∑ γ, g.inner x (kb γ) (kb γ)
    0 ≤ Q ∧ Q = (Real.sqrt Q) ^ 2 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K := curvatureOnFields_iteratedCovariantDerivative D k
  let b := g.orthonormalBasis x
  let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let kb := fun γ : Fin (k + 3) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
    K (fun r => ext (γ r)) x
  let Q := ∑ γ, g.inner x (kb γ) (kb γ)
  change 0 ≤ Q ∧ Q = (Real.sqrt Q) ^ 2
  have hQ : 0 ≤ Q := by
    apply Finset.sum_nonneg
    intro γ _
    rw [show g.inner x (kb γ) (kb γ) = ‖kb γ‖ ^ 2 from
      real_inner_self_eq_norm_sq (kb γ)]
    exact sq_nonneg _
  exact ⟨hQ, (Real.sq_sqrt hQ).symm⟩


theorem curvature_iterated_zero_orthonormal_energy_sqrt
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    let K := curvatureOnFields_iteratedCovariantDerivative D 0
    let b := g.orthonormalBasis x
    let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let kb := fun γ : Fin (0 + 3) →
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      K (fun r => ext (γ r)) x
    Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) =
      D.curvatureTensorNorm x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let R := fun i j k : ι => D.curvature x (b i) (b j) (b k)
  change Real.sqrt (∑ γ : Fin 3 → ι, g.inner x (R (γ 0) (γ 1) (γ 2))
      (R (γ 0) (γ 1) (γ 2))) =
    Real.sqrt (∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
      D.curvatureTensor x (b i) (b j) (b k) (b l) ^ 2)
  apply congrArg Real.sqrt
  let e : (ι × ι × ι) ≃ (Fin 3 → ι) :=
    Equiv.ofBijective (fun p => ![p.1, p.2.1, p.2.2]) (by
      constructor
      · intro p q h
        apply Prod.ext
        · exact congrFun h 0
        · apply Prod.ext
          · exact congrFun h 1
          · exact congrFun h 2
      · intro f
        exact ⟨(f 0, f 1, f 2), by funext i; fin_cases i <;> rfl⟩)
  have hsum : (∑ p : ι × ι × ι, g.inner x (R p.1 p.2.1 p.2.2)
      (R p.1 p.2.1 p.2.2)) =
      ∑ γ : Fin 3 → ι, g.inner x (R (γ 0) (γ 1) (γ 2))
        (R (γ 0) (γ 1) (γ 2)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [← hsum]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have houtput (k : ι) : g.inner x (R i j k) (R i j k) =
      ∑ l : ι, D.curvatureTensor x (b i) (b j) (b l) (b k) ^ 2 := by
    rw [show g.inner x (R i j k) (R i j k) = ‖R i j k‖ ^ 2 from
      real_inner_self_eq_norm_sq (R i j k)]
    have hh := (b.sum_sq_inner_left (R i j k)).symm
    change ‖R i j k‖ ^ 2 = ∑ l : ι, g.inner x (R i j k) (b l) ^ 2 at hh
    simpa only [R, LeviCivitaData.curvatureTensor] using hh
  simp_rw [houtput]
  exact Finset.sum_comm

end PoincareConjecture.Proofs.M03
