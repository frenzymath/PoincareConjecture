import PoincareConjecture.Proofs.M03.CurvatureFamily
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M03.MetricGradientEvolution
import PoincareConjecture.Proofs.M03.MetricInverse
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contDiffOn_family_metric_inner_time
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(g 0).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
    ContDiffOn ℝ ∞ (fun t => ((g t).inner x :
      TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)) J := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(g 0).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_clm_apply.mpr
  intro b
  obtain ⟨Sa, hSa, ha⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) a
  obtain ⟨Sb, hSb, hb⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) b
  obtain ⟨U, hUsub, _hU, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hSa hSb)
  have hp := contMDiffOn_family_metric_pair hg
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b)
    (ha.mono (fun _ hy => (hUsub hy).1)) (hb.mono (fun _ hy => (hUsub hy).2))
  have hi : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ => (t, x)) J := contMDiffOn_id.prodMk contMDiffOn_const
  have ht := hp.comp hi (fun _ ht => ⟨ht, hxU⟩)
  apply ContMDiffOn.contDiffOn
  simpa only [Function.comp_def, FiberBundle.extend_apply_self] using ht

theorem contDiffOn_family_curvature_time
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(g 0).toRiemannianMetric⟩
    ContDiffOn ℝ ∞ (fun t => (D t).curvature x u v w) J := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(g 0).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let G (t : ℝ) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    (g t).inner x
  let B (t : ℝ) : TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
    G t ((D t).curvature x u v w)
  have hG : ContDiffOn ℝ ∞ G J := contDiffOn_family_metric_inner_time hg x
  have hB : ContDiffOn ℝ ∞ B J := by
    apply contDiffOn_clm_apply.mpr
    intro z
    exact contDiffOn_family_curvatureTensor_time hg D x u v z w
  have hGinv (t : ℝ) : (G t).IsInvertible := by
    have hinj : Function.Injective (G t).toLinearMap := by
      intro a b hab
      apply sub_eq_zero.mp
      by_contra hne
      have heq : (g t).inner x (a - b) (a - b) = 0 := by
        have h := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (a - b)) hab
        change (g t).inner x a (a - b) = (g t).inner x b (a - b) at h
        rw [map_sub ((g t).inner x), sub_apply, h, sub_self]
      exact ((g t).pos x (a - b) hne).ne' heq
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
        Module.finrank ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
      calc
        _ = Module.finrank ℝ (Module.Dual ℝ (TangentSpace (𝓡 n) x)) :=
          Subspace.dual_finrank_eq.symm
        _ = _ := (LinearMap.toContinuousLinearMap :
          (TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
            (TangentSpace (𝓡 n) x →L[ℝ] ℝ)).finrank_eq
    exact ⟨((G t).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv, rfl⟩
  have hi : ContDiffOn ℝ ∞ (fun t => (G t).inverse) J := by
    intro t ht
    exact (hGinv t).contDiffAt_map_inverse.comp_contDiffWithinAt t (hG t ht)
  apply (hi.clm_apply hB).congr
  intro t _ht
  symm
  change (G t).inverse (G t ((D t).curvature x u v w)) = (D t).curvature x u v w
  exact congrArg (fun L => L ((D t).curvature x u v w)) (hGinv t).inverse_comp_self

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem hasDerivAt_ricciFlow_iteratedCurvature_squared_norm_frame
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (k : ℕ)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun s : ℝ => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
    let a := fun (s : ℝ) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G s) (EuclideanSpace.proj j)) i
    let K := fun s (α : Fin (k + 3) → Fin n) =>
      curvatureOnFields_iteratedCovariantDerivative (F.connection s) k (fun j => E (α j)) x
    let dotK := fun α => deriv (fun s => K s α) t
    let raised := fun i => e.symmL ℝ x ((G t).inverse (EuclideanSpace.proj i))
    let W := fun s (α β : Fin (k + 3) → Fin n) => ∏ r, a s (α r) (β r)
    HasDerivAt
      (fun s => ∑ α, ∑ β, W s α β * (F.metric s).inner x (K s α) (K s β))
      (2 * (∑ α, ∑ β, W t α β * (F.metric t).inner x (dotK α) (K t β)) -
        2 * (∑ α, ∑ β, W t α β * (F.connection t).ricci x (K t α) (K t β)) +
        ∑ α, ∑ β, ∑ r : Fin (k + 3),
          2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
            (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
              (F.metric t).inner x (K t α) (K t β)) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun s : ℝ => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
  let a := fun (s : ℝ) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G s) (EuclideanSpace.proj j)) i
  let K := fun s (α : Fin (k + 3) → Fin n) =>
    curvatureOnFields_iteratedCovariantDerivative (F.connection s) k (fun j => E (α j)) x
  let dotK := fun α => deriv (fun s => K s α) t
  let raised := fun i => e.symmL ℝ x ((G t).inverse (EuclideanSpace.proj i))
  let W := fun s (α β : Fin (k + 3) → Fin n) => ∏ r, a s (α r) (β r)
  let B := fun s : ℝ => (F.metric s).inner x
  let ric := (F.connection t).ricci x
  have htJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hB : HasDerivAt B (deriv B t) t :=
    (((contDiffOn_family_metric_inner_time F.smooth x).contDiffAt htJ).differentiableAt
      (by simp)).hasDerivAt
  have hBval (v w : TangentSpace (𝓡 n) x) : (deriv B t) v w = -2 * ric v w := by
    have hh := (hB.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
    have hh' : HasDerivAt (fun s => B s v w) ((deriv B t) v w) t := by
      simpa only [map_zero, add_zero] using hh
    exact hh'.unique ((F.equation t (interior_subset ht) x v w).hasDerivAt htJ)
  have hmetric (s : ℝ) (v w : V) :
      G s v w = B s (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    dsimp only [G, B]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx v,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
  have hInv := contMDiffOn_family_metric_frame_inverse F.smooth x0
  have hGi (s : ℝ) : (G s).IsInvertible := hInv.1 (s, x) hx
  have hmap : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
  have hGd : HasDerivAt G (deriv G t) t := by
    have hh := (hInv.2.1.contMDiffAt
      (prod_mem_nhds htJ (e.open_baseSet.mem_nhds hx))).comp t hmap
    exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hId : HasDerivAt (fun s => (G s).inverse)
      (deriv (fun s => (G s).inverse) t) t := by
    have hh := (hInv.2.2.contMDiffAt
      (prod_mem_nhds htJ (e.open_baseSet.mem_nhds hx))).comp t hmap
    exact (hh.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hGval (v w : V) :
      (deriv G t) v w = -2 * ric (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    have hd := (hGd.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t w)
    have hd' : HasDerivAt (fun s => G s v w) ((deriv G t) v w) t := by
      simpa only [map_zero, add_zero] using hd
    exact hd'.unique (((F.equation t (interior_subset ht) x
      (e.symmL ℝ x v) (e.symmL ℝ x w)).hasDerivAt htJ).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => hmetric s v w)))
  have hsymG (s : ℝ) (v w : V) : G s v w = G s w v := by
    rw [hmetric, hmetric]
    exact (F.metric s).symm x _ _
  have had (i j : Fin n) :
      HasDerivAt (fun s => a s i j) (2 * ric (raised j) (raised i)) t := by
    let v := (G t).inverse (EuclideanSpace.proj i)
    let w := (G t).inverse (EuclideanSpace.proj j)
    let wd := (deriv (fun s => (G s).inverse) t) (EuclideanSpace.proj j)
    have hw : HasDerivAt (fun s => (G s).inverse (EuclideanSpace.proj j)) wd t := by
      simpa only [map_zero, add_zero] using hId.clm_apply
        (hasDerivAt_const t (EuclideanSpace.proj j))
    have hzero : (deriv G t) w v + G t wd v = 0 := by
      have hd := (hGd.clm_apply hw).clm_apply (hasDerivAt_const t v)
      have heq : (fun _ : ℝ => (EuclideanSpace.proj j) v) =ᶠ[𝓝 t]
          (fun s => G s ((G s).inverse (EuclideanSpace.proj j)) v) := by
        filter_upwards [] with s
        exact (congrArg (fun L : V →L[ℝ] ℝ => L v)
          ((hGi s).self_apply_inverse (EuclideanSpace.proj j))).symm
      have hd' : HasDerivAt (fun _ : ℝ => (EuclideanSpace.proj j) v)
          ((deriv G t) w v + G t wd v) t := by
        simpa only [w, map_zero, add_zero, add_apply] using hd.congr_of_eventuallyEq heq
      exact hd'.unique (hasDerivAt_const t _)
    have hsecond : G t wd v = wd i := by
      rw [hsymG]
      exact congrArg (fun L : V →L[ℝ] ℝ => L wd)
        ((hGi t).self_apply_inverse (EuclideanSpace.proj i))
    rw [hGval, hsecond] at hzero
    have hd : HasDerivAt (fun s => a s i j) (wd i) t := by
      have hh := (EuclideanSpace.proj i : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
      change HasDerivAt (fun s => a s i j) (wd i) t at hh
      exact hh
    apply hd.congr_deriv
    change wd i = 2 * ric (e.symmL ℝ x w) (e.symmL ℝ x v)
    linarith
  have hasymm (i j : Fin n) : a t i j = a t j i := by
    calc
      a t i j = G t ((G t).inverse (EuclideanSpace.proj i))
          ((G t).inverse (EuclideanSpace.proj j)) := by
        rw [(hGi t).self_apply_inverse]
        rfl
      _ = G t ((G t).inverse (EuclideanSpace.proj j))
          ((G t).inverse (EuclideanSpace.proj i)) := hsymG _ _ _
      _ = a t j i := by
        rw [(hGi t).self_apply_inverse]
        rfl
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hKd (α : Fin (k + 3) → Fin n) : HasDerivAt (fun s => K s α) (dotK α) t := by
    have hh := contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun j _ => E (α j))
      (fun j => (hE (α j)).comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun _ hp => hp.2))
    exact (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
        (fun j => E (α j))) hh ht).1 x hx
  have hWd (α β : Fin (k + 3) → Fin n) : HasDerivAt (fun s => W s α β)
      (∑ r : Fin (k + 3), (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
        (2 * ric (raised (β r)) (raised (α r)))) t := by
    simpa only [W, smul_eq_mul] using HasDerivAt.fun_finsetProd
      (u := (Finset.univ : Finset (Fin (k + 3)))) (fun r _ => had (α r) (β r))
  have hp (α β : Fin (k + 3) → Fin n) : HasDerivAt
      (fun s => B s (K s α) (K s β))
      (-2 * ric (K t α) (K t β) + B t (dotK α) (K t β) +
        B t (K t α) (dotK β)) t := by
    have hd := (hB.clm_apply (hKd α)).clm_apply (hKd β)
    apply hd.congr_deriv
    simp only [add_apply, hBval]
  have hWsymm (α β : Fin (k + 3) → Fin n) : W t α β = W t β α := by
    apply Finset.prod_congr rfl
    intro r _
    exact hasymm _ _
  have hpair : (∑ α, ∑ β, W t α β * B t (K t α) (dotK β)) =
      ∑ α, ∑ β, W t α β * B t (dotK α) (K t β) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    rw [hWsymm β α, (F.metric t).symm]
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (k + 3) → Fin n)))
    (fun α _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (k + 3) → Fin n)))
      (fun β _ => (hWd α β).mul (hp α β)))
  change HasDerivAt
    (fun s => ∑ α, ∑ β, W s α β * B s (K s α) (K s β))
    (2 * (∑ α, ∑ β, W t α β * B t (dotK α) (K t β)) -
      2 * (∑ α, ∑ β, W t α β * ric (K t α) (K t β)) +
      ∑ α, ∑ β, ∑ r : Fin (k + 3),
        2 * ric (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
            B t (K t α) (K t β)) t
  apply hd.congr_deriv
  change (∑ α, ∑ β,
      ((∑ r : Fin (k + 3), (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
          (2 * ric (raised (β r)) (raised (α r)))) * B t (K t α) (K t β) +
        W t α β * (-2 * ric (K t α) (K t β) + B t (dotK α) (K t β) +
          B t (K t α) (dotK β)))) = _
  simp only [Finset.sum_add_distrib, mul_add]
  rw [hpair]
  have htime : (∑ α, ∑ β,
      (∑ r : Fin (k + 3), (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) *
        (2 * ric (raised (β r)) (raised (α r)))) * B t (K t α) (K t β)) =
      ∑ α, ∑ β, ∑ r : Fin (k + 3),
        2 * ric (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t (α s) (β s)) * B t (K t α) (K t β) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [htime]
  have hneg : (∑ α, ∑ β, W t α β * (-2 * ric (K t α) (K t β))) =
      -2 * (∑ α, ∑ β, W t α β * ric (K t α) (K t β)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hneg]
  ring

set_option maxHeartbeats 3600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_all_rank_metric_rate_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (rank : ℕ) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (v : (Fin rank → Fin n) → TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let W := fun α β : Fin rank → Fin n => ∏ r, a (α r) (β r)
    let raised := fun i => e.symmL ℝ x (G.inverse (EuclideanSpace.proj i))
    let q := ∑ α, ∑ β, W α β * g.inner x (v α) (v β);
    -2 * (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) +
      (∑ α, ∑ β, ∑ r : Fin rank, 2 * D.ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) ≤
      (2 * (n : ℝ) + 2 * (rank : ℝ) * (n : ℝ) ^ 2) * D.curvatureTensorNorm x * q := by
  classical
  have inputMetricSlotWeight
      {ι κ : Type} [Fintype ι] [Fintype κ]
      (theta : ι → κ → ℝ) (ric : κ → κ → ℝ) (r : Fin rank)
      (α β : Fin rank → ι) :
      let a := fun i j => ∑ p, theta i p * theta j p
      let d := fun (γ : Fin rank → κ) (δ : Fin rank → ι) => ∏ s, theta (δ s) (γ s)
      let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
      (∑ γ : Fin rank → κ, ∑ p : κ,
        ric p (γ r) * d γ α * d (Function.update γ r p) β) =
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * h (α r) (β r) := by
    classical
    let a := fun i j => ∑ p, theta i p * theta j p
    let d := fun (γ : Fin rank → κ) (δ : Fin rank → ι) => ∏ s, theta (δ s) (γ s)
    let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
    let rest := fun γ : Fin rank → κ =>
      ∏ s ∈ Finset.univ.erase r, theta (α s) (γ s) * theta (β s) (γ s)
    let weight := ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
    have hd (γ : Fin rank → κ) (δ : Fin rank → ι) :
        d γ δ = theta (δ r) (γ r) *
          ∏ s ∈ Finset.univ.erase r, theta (δ s) (γ s) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ r)).symm
    have hterm (γ : Fin rank → κ) (p : κ) :
        d γ α * d (Function.update γ r p) β =
          (theta (α r) (γ r) * theta (β r) p) * rest γ := by
      rw [hd, hd, Function.update_self]
      have hp : (∏ s ∈ Finset.univ.erase r,
          theta (β s) (Function.update γ r p s)) =
          ∏ s ∈ Finset.univ.erase r, theta (β s) (γ s) := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
      rw [hp]
      dsimp only [rest]
      rw [Finset.prod_mul_distrib]
      ring
    have hsep (c : κ → ℝ) :
        (∑ γ : Fin rank → κ, c (γ r) * rest γ) = (∑ p, c p) * weight := by
      let f := fun (s : Fin rank) (i : κ) =>
        if s = r then c i else theta (α s) i * theta (β s) i
      have hf (γ : Fin rank → κ) :
          (∏ s, f s (γ s)) = c (γ r) * rest γ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
        simp only [f, ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro s hs
        rw [if_neg (Finset.mem_erase.mp hs).1]
      have hfs : (∏ s : Fin rank, ∑ i : κ, f s i) = (∑ i, c i) * weight := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
        simp only [f, ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro s hs
        simp only [if_neg (Finset.mem_erase.mp hs).1]
        rfl
      calc
        _ = ∑ γ : Fin rank → κ, ∏ s, f s (γ s) := by simp only [hf]
        _ = ∏ s : Fin rank, ∑ i : κ, f s i := (Fintype.prod_sum f).symm
        _ = _ := hfs
    change (∑ γ : Fin rank → κ, ∑ p : κ,
        ric p (γ r) * d γ α * d (Function.update γ r p) β) = weight * h (α r) (β r)
    calc
      _ = ∑ p : κ, ∑ γ : Fin rank → κ,
          (theta (α r) (γ r) * theta (β r) p * ric p (γ r)) * rest γ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro γ _
        calc
          _ = ric p (γ r) * (d γ α * d (Function.update γ r p) β) := by ring
          _ = _ := by rw [hterm]; ring
      _ = ∑ p : κ, (∑ q : κ, theta (α r) q * theta (β r) p * ric p q) * weight := by
        apply Finset.sum_congr rfl
        intro p _
        exact hsep (fun q => theta (α r) q * theta (β r) p * ric p q)
      _ = weight * h (α r) (β r) := by
        dsimp only [h]
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        ring
  have inputMetricSlotContraction
      {ι κ Z : Type} [Fintype ι] [Fintype κ]
      [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (B : Z →L[ℝ] Z →L[ℝ] ℝ)
      (theta : ι → κ → ℝ) (ric : κ → κ → ℝ) (r : Fin rank)
      (v : (Fin rank → ι) → Z) :
      let a := fun i j => ∑ p, theta i p * theta j p
      let d := fun (γ : Fin rank → κ) (δ : Fin rank → ι) => ∏ s, theta (δ s) (γ s)
      let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
      let V := fun γ => ∑ α, d γ α • v α
      (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        h (α r) (β r) * B (v α) (v β)) =
        ∑ γ : Fin rank → κ, ∑ p : κ,
          ric p (γ r) * B (V γ) (V (Function.update γ r p)) := by
    classical
    let a := fun i j => ∑ p, theta i p * theta j p
    let d := fun (γ : Fin rank → κ) (δ : Fin rank → ι) => ∏ s, theta (δ s) (γ s)
    let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
    let V := fun γ => ∑ α, d γ α • v α
    have hweight (α β : Fin rank → ι) :
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * h (α r) (β r) =
          ∑ γ : Fin rank → κ, ∑ p : κ,
            ric p (γ r) * d γ α * d (Function.update γ r p) β :=
      (inputMetricSlotWeight theta ric r α β).symm
    have hswap (f : (Fin rank → ι) → (Fin rank → ι) → (Fin rank → κ) → κ → ℝ) :
        (∑ α, ∑ β, ∑ γ, ∑ p, f α β γ p) = ∑ γ, ∑ p, ∑ α, ∑ β, f α β γ p := by
      calc
        _ = ∑ α, ∑ γ, ∑ β, ∑ p, f α β γ p := by
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
        _ = ∑ γ, ∑ α, ∑ β, ∑ p, f α β γ p := Finset.sum_comm
        _ = ∑ γ, ∑ α, ∑ p, ∑ β, f α β γ p := by
          apply Finset.sum_congr rfl
          intro γ _
          apply Finset.sum_congr rfl
          intro α _
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro γ _
          exact Finset.sum_comm
    change (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        h (α r) (β r) * B (v α) (v β)) =
        ∑ γ : Fin rank → κ, ∑ p : κ,
          ric p (γ r) * B (V γ) (V (Function.update γ r p))
    calc
      _ = ∑ α, ∑ β, (∑ γ : Fin rank → κ, ∑ p : κ,
          ric p (γ r) * d γ α * d (Function.update γ r p) β) * B (v α) (v β) := by
        simp only [hweight]
      _ = ∑ γ : Fin rank → κ, ∑ p : κ, ∑ α, ∑ β,
          (ric p (γ r) * d γ α * d (Function.update γ r p) β) * B (v α) (v β) := by
        simp only [Finset.sum_mul]
        exact hswap _
      _ = _ := by
        dsimp only [V]
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        apply Finset.sum_congr rfl
        intro p _
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let W := fun α β : Fin rank → Fin n => ∏ r, a (α r) (β r)
  let raised := fun i => e.symmL ℝ x (G.inverse (EuclideanSpace.proj i))
  let q := ∑ α, ∑ β, W α β * g.inner x (v α) (v β)
  let A := D.curvatureTensorNorm x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let d := fun (γ : Fin rank → ι) (α : Fin rank → Fin n) =>
    ∏ r, theta (α r) x (b (γ r))
  let z := fun γ : Fin rank → ι => ∑ α, d γ α • v α
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hdim : Fintype.card ι = n := by
    simp only [ι, Fintype.card_fin]
    rw [VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) x,
      finrank_euclideanSpace_fin]
  have hnorm (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w = ‖w‖ := by
    rw [RiemannianMetric.tangentNorm, show g.inner x w w = ‖w‖ ^ 2 from
      real_inner_self_eq_norm_sq w, Real.sqrt_sq (norm_nonneg _)]
  have htrace (i j : Fin n) : a i j = ∑ p, theta i x (b p) * theta j x (b p) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hWeight (α β : Fin rank → Fin n) :
      W α β = ∑ γ : Fin rank → ι, d γ α * d γ β := by
    dsimp only [W]
    simp_rw [htrace]
    rw [Fintype.prod_sum]
    simp only [d, Finset.prod_mul_distrib]
    rfl
  have hfull (B : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
      (∑ γ, B (z γ) (z γ)) = ∑ α, ∑ β, W α β * B (v α) (v β) := by
    have hex (γ : Fin rank → ι) : B (z γ) (z γ) =
        ∑ α, ∑ β, (d γ α * d γ β) * B (v α) (v β) := by
      dsimp only [z]
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      ring
    simp only [hex]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [← Finset.sum_mul, ← hWeight]
  have hq : q = ∑ γ, ‖z γ‖ ^ 2 := by
    rw [show q = ∑ γ, g.inner x (z γ) (z γ) from (hfull (g.inner x)).symm]
    exact Finset.sum_congr rfl fun γ _ => real_inner_self_eq_norm_sq (z γ)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ V (TangentSpace (𝓡 n)) x
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  let tr : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    { toFun := fun u => ∑ i, T u (b i) (b i)
      map_add' := by
        intro u w
        simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum, RingHom.id_apply] }
  let Ric := (g.inner x).comp (LinearMap.toContinuousLinearMap tr)
  have hRic (u w : TangentSpace (𝓡 n) x) : Ric u w = D.ricci x u w := by
    change g.inner x (∑ p, T u (b p) (b p)) w =
      ∑ p, D.curvatureTensor x u (b p) w (b p)
    simp only [map_sum, sum_apply, hT, LeviCivitaData.curvatureTensor]
  have hout : (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) =
      ∑ γ, D.ricci x (z γ) (z γ) := by
    simpa only [hRic] using (hfull Ric).symm
  have htheta (p : Fin n) (w : TangentSpace (𝓡 n) x) :
      theta p x w = (e.continuousLinearMapAt ℝ x w) p := by
    have hh := e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) cb hx
      (FiberBundle.extend V w) p
    rw [FiberBundle.extend_apply_self] at hh
    change theta p x w = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, cb, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
    rfl
  have hmetric (u w : V) : G u w = g.inner x (e.symmL ℝ x u) (e.symmL ℝ x w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx u,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  have hfamily : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) Set.univ :=
    (g.contMDiff.comp contMDiff_snd).contMDiffOn
  have hGi : G.IsInvertible :=
    (contMDiffOn_family_metric_frame_inverse hfamily x0).1 (0, x) hx
  have hpair (i : Fin n) (w : TangentSpace (𝓡 n) x) :
      g.inner x (raised i) w = theta i x w := by
    calc
      _ = G (G.inverse (EuclideanSpace.proj i)) (e.continuousLinearMapAt ℝ x w) := by
        rw [hmetric, Trivialization.symmL_continuousLinearMapAt _ hx]
      _ = (e.continuousLinearMapAt ℝ x w) i := by rw [hGi.self_apply_inverse]; rfl
      _ = _ := (htheta i w).symm
  have hraised (i : Fin n) : raised i = ∑ p, theta i x (b p) • b p := by
    have hh := b.sum_repr' (raised i)
    change (∑ p, g.inner x (b p) (raised i) • b p) = raised i at hh
    simpa only [g.symm x, hpair] using hh.symm
  have hentry (i j : Fin n) : D.ricci x (raised j) (raised i) =
      ∑ p, ∑ q, D.ricci x (b p) (b q) * theta i x (b q) * theta j x (b p) := by
    rw [← hRic, hraised j, hraised i]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [hRic]
    ring
  have hinput (r : Fin rank) :
      (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β)) =
      ∑ γ, ∑ p, D.ricci x (b p) (b (γ r)) *
        g.inner x (z γ) (z (Function.update γ r p)) := by
    simpa only [htrace, hentry] using inputMetricSlotContraction (g.inner x)
      (fun i p => theta i x (b p)) (fun p q => D.ricci x (b p) (b q)) r v
  have hric (u w : TangentSpace (𝓡 n) x) :
      |D.ricci x u w| ≤ (n : ℝ) * A * ‖u‖ * ‖w‖ := by
    simpa only [hnorm] using abs_ricci_le_curvatureTensorNorm D x u w
  have hricBasis (i j : ι) : |D.ricci x (b i) (b j)| ≤ (n : ℝ) * A := by
    simpa only [b.norm_eq_one, mul_one] using hric (b i) (b j)
  have hslot (r : Fin rank) :
      (∑ γ, ∑ p, ‖z γ‖ * ‖z (Function.update γ r p)‖) ≤ (n : ℝ) * q := by
    let swap := fun s : (Fin rank → ι) × ι => (Function.update s.1 r s.2, s.1 r)
    have hs : Function.Involutive swap := by
      intro s
      apply Prod.ext
      · funext j
        by_cases hj : j = r
        · subst j
          simp [swap]
        · simp [swap, Function.update_of_ne hj]
      · simp [swap]
    let eqv : ((Fin rank → ι) × ι) ≃ ((Fin rank → ι) × ι) :=
      { toFun := swap, invFun := swap, left_inv := hs, right_inv := hs }
    have hswap : (∑ γ, ∑ p, ‖z (Function.update γ r p)‖ ^ 2) =
        ∑ γ, ∑ _p : ι, ‖z γ‖ ^ 2 := by
      have hh := eqv.sum_comp (fun s => ‖z s.1‖ ^ 2)
      change (∑ s : (Fin rank → ι) × ι, ‖z (Function.update s.1 r s.2)‖ ^ 2) =
        ∑ s : (Fin rank → ι) × ι, ‖z s.1‖ ^ 2 at hh
      simpa only [Fintype.sum_prod_type] using hh
    have hcard : (∑ γ, ∑ _p : ι, ‖z γ‖ ^ 2) = (n : ℝ) * q := by
      rw [hq]
      simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul, Finset.mul_sum]
    have hh : (∑ γ, ∑ p, 2 * (‖z γ‖ * ‖z (Function.update γ r p)‖)) ≤
        ∑ γ, ∑ p, (‖z γ‖ ^ 2 + ‖z (Function.update γ r p)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro γ _
      apply Finset.sum_le_sum
      intro p _
      nlinarith [sq_nonneg (‖z γ‖ - ‖z (Function.update γ r p)‖)]
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hh ⊢
    rw [hswap, hcard] at hh
    linarith
  have houtputBound : -2 * (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) ≤
      2 * (n : ℝ) * A * q := by
    rw [hout, hq, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ _
    have hh := (neg_le_abs (D.ricci x (z γ) (z γ))).trans (hric (z γ) (z γ))
    nlinarith only [hh]
  have hinputBound (r : Fin rank) :
      (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β)) ≤
      (n : ℝ) ^ 2 * A * q := by
    rw [hinput]
    calc
      _ ≤ ∑ γ, ∑ p, (n : ℝ) * A * (‖z γ‖ * ‖z (Function.update γ r p)‖) := by
        apply Finset.sum_le_sum
        intro γ _
        apply Finset.sum_le_sum
        intro p _
        calc
          _ ≤ |D.ricci x (b p) (b (γ r)) *
              g.inner x (z γ) (z (Function.update γ r p))| := le_abs_self _
          _ = |D.ricci x (b p) (b (γ r))| *
              |g.inner x (z γ) (z (Function.update γ r p))| := abs_mul _ _
          _ ≤ ((n : ℝ) * A) * (‖z γ‖ * ‖z (Function.update γ r p)‖) :=
            mul_le_mul (hricBasis p (γ r)) (by
              change |inner ℝ (z γ) (z (Function.update γ r p))| ≤ _
              exact abs_real_inner_le_norm _ _)
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = ((n : ℝ) * A) * ∑ γ, ∑ p, ‖z γ‖ * ‖z (Function.update γ r p)‖ := by
        simp only [Finset.mul_sum]
      _ ≤ ((n : ℝ) * A) * ((n : ℝ) * q) :=
        mul_le_mul_of_nonneg_left (hslot r) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by ring
  have hall : (∑ α, ∑ β, ∑ r : Fin rank,
      2 * D.ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) =
      ∑ r : Fin rank, 2 * (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β)) := by
    calc
      _ = ∑ α, ∑ r : Fin rank, ∑ β,
          2 * D.ricci x (raised (β r)) (raised (α r)) *
            (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β) := by
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  have hallBound : (∑ r : Fin rank, 2 * (∑ α, ∑ β,
      (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β))) ≤
      2 * (rank : ℝ) * (n : ℝ) ^ 2 * A * q := by
    calc
      _ ≤ ∑ _r : Fin rank, 2 * ((n : ℝ) ^ 2 * A * q) :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hinputBound r) (by norm_num)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  change -2 * (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) +
    (∑ α, ∑ β, ∑ r : Fin rank, 2 * D.ricci x (raised (β r)) (raised (α r)) *
      (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) ≤
    (2 * (n : ℝ) + 2 * (rank : ℝ) * (n : ℝ) ^ 2) * A * q
  rw [hall]
  nlinarith only [houtputBound, hallBound]


theorem ricciFlow_iteratedCurvature_scalar_heat_identity
    {I : Set ℝ} (F : RicciFlow n M I) {t : ℝ} (ht : t ∈ interior I) (order : ℕ)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
    let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
      ((G s y).inverse (EuclideanSpace.proj j)) i
    let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Q y (P y)
    let T := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let W := fun s y (α β : Fin (order + 3) → Fin n) => ∏ r, a s y (α r) (β r)
    let pair := fun s (y : M)
        (v w : (Fin (order + 3) → Fin n) → TangentSpace (𝓡 n) y) =>
      ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
    let k := fun s (α : Fin (order + 3) → Fin n) =>
      T s order (fun r => E (α r))
    let k1 := fun i (α : Fin (order + 3) → Fin n) =>
      T t (order + 1) (Fin.cons (E i) (fun r => E (α r)))
    let k2 := fun i j (α : Fin (order + 3) → Fin n) =>
      T t (order + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r))))
    let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
    deriv (fun s => q s x) t -
        (∑ i, ∑ j, a t x i j *
          (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
      -2 * (∑ i, ∑ j, a t x i j *
        pair t x (fun α => k1 i α x) (fun α => k1 j α x)) +
      2 * pair t x
        (fun α => deriv (fun s => k s α x) t - ∑ i, ∑ j, a t x i j • k2 i j α x)
        (fun α => k t α x) -
      2 * (∑ α, ∑ β, W t x α β * (F.connection t).ricci x (k t α x) (k t β x)) +
      ∑ α, ∑ β, ∑ r : Fin (order + 3),
        2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
            (F.metric t).inner x (k t α x) (k t β x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
  let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
    ((G s y).inverse (EuclideanSpace.proj j)) i
  let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Q y (P y)
  let T := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let W := fun s y (α β : Fin (order + 3) → Fin n) => ∏ r, a s y (α r) (β r)
  let pair := fun s (y : M)
      (v w : (Fin (order + 3) → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
  let k := fun s (α : Fin (order + 3) → Fin n) =>
    T s order (fun r => E (α r))
  let k1 := fun i (α : Fin (order + 3) → Fin n) =>
    T t (order + 1) (Fin.cons (E i) (fun r => E (α r)))
  let k2 := fun i j (α : Fin (order + 3) → Fin n) =>
    T t (order + 2) (Fin.cons (E i) (Fin.cons (E j) (fun r => E (α r))))
  let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
  let dotk := fun α => deriv (fun s => k s α x) t
  let diff := fun α => ∑ i, ∑ j, a t x i j • k2 i j α x
  let G2 := ∑ i, ∑ j, a t x i j *
    pair t x (fun α => k1 i α x) (fun α => k1 j α x)
  let C2 := ∑ i, ∑ j, a t x i j *
    pair t x (fun α => k2 i j α x) (fun α => k t α x)
  let outputRate := ∑ α, ∑ β,
    W t x α β * (F.connection t).ricci x (k t α x) (k t β x)
  let inputRate := ∑ α, ∑ β, ∑ r : Fin (order + 3),
      2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
          (F.metric t).inner x (k t α x) (k t β x)
  have htime := (hasDerivAt_ricciFlow_iteratedCurvature_squared_norm_frame
    F ht order x0 hx).deriv
  change deriv (fun s => q s x) t =
    2 * pair t x dotk (fun α => k t α x) - 2 * outputRate + inputRate at htime
  have hspace := curvature_iterated_bochner_local_frame (F.connection t) order x0 hx
  change (∑ i, ∑ j, a t x i j *
      (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
    2 * G2 + 2 * C2 at hspace
  have hlinear {A B Z : Type} [Fintype A] [Fintype B]
      [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (L : Z →L[ℝ] Z →L[ℝ] ℝ) (w : A → A → ℝ) (c : B → B → ℝ)
      (v z : A → Z) (h : B → B → A → Z) :
      (∑ α, ∑ β, w α β * L (v α - ∑ i, ∑ j, c i j • h i j α) (z β)) =
        (∑ α, ∑ β, w α β * L (v α) (z β)) -
        ∑ i, ∑ j, c i j * (∑ α, ∑ β, w α β * L (h i j α) (z β)) := by
    simp only [map_sub, map_sum, map_smul, sub_apply, sum_apply, smul_apply,
      smul_eq_mul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = ∑ α, ∑ i, ∑ β, ∑ j, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ i, ∑ α, ∑ β, ∑ j, w α β * (c i j * L (h i j α) (z β)) :=
        Finset.sum_comm
      _ = ∑ i, ∑ α, ∑ j, ∑ β, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ α, ∑ β, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  have hdiff : pair t x (fun α => dotk α - diff α) (fun α => k t α x) =
      pair t x dotk (fun α => k t α x) - C2 :=
    hlinear (A := Fin (order + 3) → Fin n) (B := Fin n) (Z := TangentSpace (𝓡 n) x)
      ((F.metric t).inner x) (W t x) (a t x) dotk
      (fun α => k t α x) (fun i j α => k2 i j α x)
  change deriv (fun s => q s x) t -
      (∑ i, ∑ j, a t x i j *
        (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
    -2 * G2 + 2 * pair t x (fun α => dotk α - diff α) (fun α => k t α x) -
      2 * outputRate + inputRate
  rw [htime, hspace, hdiff]
  ring

theorem contMDiffAt_ricciFlow_iteratedCurvature_orthonormal_energy
    {J : Set ℝ} (F : RicciFlow n M J) (k : ℕ)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let Q := fun (s : ℝ) (y : M) =>
      let b := (F.metric s).orthonormalBasis y
      let ext := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
      let K := curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
      ∑ γ : Fin (k + 3) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)),
        (F.metric s).inner y (K (fun r => ext (γ r)) y) (K (fun r => ext (γ r)) y)
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => Q p.1 p.2) (t, x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun p : ℝ × M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x p.2 x p.2 ((F.metric p.1).inner p.2)
  let a := fun (p : ℝ × M) (i j : Fin n) => ((G p).inverse (EuclideanSpace.proj j)) i
  let K := fun (s : ℝ) (α : Fin (k + 3) → Fin n) =>
    curvatureOnFields_iteratedCovariantDerivative (F.connection s) k (fun r => E (α r))
  let q := fun p : ℝ × M => ∑ α : Fin (k + 3) → Fin n,
    ∑ β : Fin (k + 3) → Fin n, (∏ r, a p (α r) (β r)) *
      (F.metric p.1).inner p.2 (K p.1 α p.2) (K p.1 β p.2)
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i
  have hK (α : Fin (k + 3) → Fin n) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (fun p : ℝ × M => Bundle.TotalSpace.mk' V p.2 (K p.1 α p.2))
        (J ×ˢ e.baseSet) := by
    apply contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun r _ => E (α r))
    intro r
    exact (hE (α r)).comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
      (fun _ hp => hp.2)
  have hpair (α β : Fin (k + 3) → Fin n) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (F.metric p.1).inner p.2 (K p.1 α p.2) (K p.1 β p.2))
        (J ×ˢ e.baseSet) := by
    have hp := ContMDiffOn.clm_bundle_apply₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := fun y : M => TangentSpace (𝓡 n) y)
      (E₂ := fun y : M => TangentSpace (𝓡 n) y) (E₃ := fun _ : M => ℝ)
      (ψ := fun p : ℝ × M => (F.metric p.1).inner p.2) (b := Prod.snd)
      (F.smooth.mono (Set.prod_mono subset_rfl (subset_univ e.baseSet))) (hK α) (hK β)
    intro p hpS
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hp p hpS)).2
  have hinv := (contMDiffOn_family_metric_frame_inverse F.smooth x).2.2
  have ha (i j : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => a p i j) (J ×ˢ e.baseSet) :=
    (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hinv.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hq : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ q
      (J ×ˢ e.baseSet) := by
    apply contMDiffOn_finsetSum
    intro α _
    apply contMDiffOn_finsetSum
    intro β _
    exact (contMDiffOn_finsetProd (fun r _ => ha (α r) (β r))).mul (hpair α β)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hdom : J ×ˢ e.baseSet ∈ 𝓝 (t, x) :=
    prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) (e.open_baseSet.mem_nhds hx)
  apply (hq.contMDiffAt hdom).congr_of_eventuallyEq
  filter_upwards [hdom] with p hp
  exact (curvature_iterated_squared_norm_frame_eq_orthonormal
    (F.connection p.1) k x hp.2).symm

end PoincareConjecture.Proofs.M03
