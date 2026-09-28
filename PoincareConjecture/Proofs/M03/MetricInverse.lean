import PoincareConjecture.Proofs.M03.MetricCompactBounds
import PoincareConjecture.Proofs.M03.CurvatureFrameCoordinate










set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem isInvertible_bilinear_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) : B.IsInvertible := by
  have hzero (v : E) (hv : B v = 0) : v = 0 := by
    by_contra hne
    have hp := hpos v hne
    rw [hv] at hp
    simp at hp
  have hinj : Function.Injective B.toLinearMap := by
    intro v w hvw
    have hz : B (v - w) = 0 := by
      change B.toLinearMap (v - w) = 0
      rw [map_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hzero (v - w) hz)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Module.Dual ℝ E) := Subspace.dual_finrank_eq.symm
      _ = _ := (LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
  let j : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    (B.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  refine ⟨j, ?_⟩
  ext v w
  rfl

theorem exists_pos_uniform_bilinear_inverse_bounds
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {K : Set X}
    (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K,
      ‖B x‖ ≤ C ∧ ‖ContinuousLinearMap.inverse (B x)‖ ≤ C ∧
      ∀ l : E →L[ℝ] ℝ,
        c * ‖l‖ ^ 2 ≤ l (ContinuousLinearMap.inverse (B x) l) ∧
        l (ContinuousLinearMap.inverse (B x) l) ≤ C * ‖l‖ ^ 2 := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
  have hBi (x : X) (hx : x ∈ K) : (B x).IsInvertible :=
    isInvertible_bilinear_of_pos (hpos x hx)
  have hI : ContinuousOn (fun x => (B x).inverse) K := by
    intro x hx
    exact ((hBi x hx).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
      (hB x hx)
  let H (x : X) : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ).comp ((B x).inverse)
  have hH : ContinuousOn H K := continuousOn_const.clm_comp hI
  have hposH (x : X) (hx : x ∈ K) (l : E →L[ℝ] ℝ) (hl : l ≠ 0) :
      0 < H x l l := by
    let v := (B x).inverse l
    have hbv : B x v = l := (hBi x hx).self_apply_inverse l
    have hv : v ≠ 0 := by
      intro hz
      apply hl
      rw [← hbv, hz, map_zero]
    change 0 < l v
    rw [← hbv]
    exact hpos x hx v hv
  obtain ⟨c, C₀, hc, hC₀, hdiag⟩ := exists_pos_uniform_bilinear_bounds hK hH hposH
  obtain ⟨C₁, hC₁⟩ := hK.bddAbove_image hB.norm
  obtain ⟨C₂, hC₂⟩ := hK.bddAbove_image hI.norm
  refine ⟨c, max C₀ (max C₁ C₂), hc, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · exact (hC₁ (Set.mem_image_of_mem (fun x => ‖B x‖) hx)).trans
      ((le_max_left C₁ C₂).trans (le_max_right C₀ _))
  · exact (hC₂ (Set.mem_image_of_mem (fun x => ‖(B x).inverse‖) hx)).trans
      ((le_max_right C₁ C₂).trans (le_max_right C₀ _))
  · intro l
    have hd := hdiag x hx l
    change c * ‖l‖ ^ 2 ≤ l ((B x).inverse l) ∧
      l ((B x).inverse l) ≤ C₀ * ‖l‖ ^ 2 at hd
    exact ⟨hd.1, hd.2.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_family_metric_frame_inverse
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (x₀ : M) :
    let e := trivializationAt
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
    let G := fun q : ℝ × M =>
      ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        x₀ q.2 x₀ q.2 ((g q.1).inner q.2)
    (∀ q : ℝ × M, q.2 ∈ e.baseSet → (G q).IsInvertible) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ G (J ×ˢ e.baseSet) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        𝓘(ℝ, (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ]
          EuclideanSpace ℝ (Fin n)) ∞
        (fun q => ContinuousLinearMap.inverse (G q)) (J ×ˢ e.baseSet) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
  let G := fun q : ℝ × M =>
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      x₀ q.2 x₀ q.2 ((g q.1).inner q.2)
  let frame (a : EuclideanSpace ℝ (Fin n)) (x : M) : TangentSpace (𝓡 n) x :=
    e.symmL ℝ x a
  have hframe (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro x hx
    simpa [frame, Trivialization.symmL_apply _ hx] using
      congrArg Prod.snd (e.apply_mk_symm hx a)
  have heval (q : ℝ × M) (hq : q.2 ∈ e.baseSet)
      (a b : EuclideanSpace ℝ (Fin n)) :
      G q a b = (g q.1).inner q.2 (frame a q.2) (frame b q.2) := by
    dsimp [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hq hq (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hq a,
      ← Trivialization.symmL_apply (R := ℝ) e hq b]
    simp [frame]
  have hGi (q : ℝ × M) (hq : q.2 ∈ e.baseSet) : (G q).IsInvertible := by
    apply isInvertible_bilinear_of_pos
    intro a ha
    rw [heval q hq a a]
    apply (g q.1).pos q.2
    intro hz
    have heq := congrArg (e.continuousLinearMapAt ℝ q.2) hz
    change e.continuousLinearMapAt ℝ q.2 (e.symmL ℝ q.2 a) =
      e.continuousLinearMapAt ℝ q.2 0 at heq
    rw [Trivialization.continuousLinearMapAt_symmL _ hq, map_zero] at heq
    exact ha heq
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ G (J ×ˢ e.baseSet) := by
    intro q hq
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro a
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro b
    have hpair : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p => G p a b) (J ×ˢ e.baseSet) :=
      (contMDiffOn_family_metric_pair hg (frame a) (frame b) (hframe a) (hframe b)).congr
        (fun p hp => heval p hp.2 a b)
    exact hpair q hq
  refine ⟨hGi, hG, ?_⟩
  intro q hq
  exact ContMDiffAt.comp_contMDiffWithinAt q
    ((hGi q hq.2).contDiffAt_map_inverse.contMDiffAt) (hG q hq)


theorem metric_inverse_covariant_derivative_coordinates
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame b
    let theta := e.localFrameCoeff (𝓡 n) b
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (g.inner y)
    let a := fun (y : M) (j k : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj k)) j
    let Gamma := fun (y : M) (i p j : Fin n) =>
      theta j y (D.connection (E p) y (E i y))
    ∀ z ∈ c.target, ∀ i j k : Fin n,
      let x := c.symm z
      fderiv ℝ (fun w => a (c.symm w) j k) z (EuclideanSpace.single i 1) =
        -(∑ p, (Gamma x i p j * a x p k + Gamma x i p k * a x j p)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
  let a := fun (y : M) (j k : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj k)) j
  let Gamma := fun (y : M) (i p j : Fin n) =>
    theta j y (D.connection (E p) y (E i y))
  let raised := fun (j : Fin n) (y : M) =>
    e.symmL ℝ y (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j))
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hframe (i : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      E i y = e.symmL ℝ y (EuclideanSpace.single i 1) := by
    change e.localFrame b i y = _
    rw [e.localFrame_apply_of_mem_baseSet b hy]
    simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    rw [Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hy]
  have hthetaFrame (i p : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      theta i y (E p y) = if p = i then 1 else 0 := by
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hy (E p) i]
    change ((e.basisAt b hy).repr (e.localFrame b p y)) i = _
    rw [e.localFrame_apply_of_mem_baseSet b hy]
    exact Module.Basis.repr_self_apply _ _ _
  have hfamily : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) Set.univ :=
    (g.contMDiff.comp contMDiff_snd).contMDiffOn
  have hInv := contMDiffOn_family_metric_frame_inverse hfamily x0
  have hGi {y : M} (hy : y ∈ e.baseSet) : (G y).IsInvertible := hInv.1 (0, y) hy
  have hIsmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, (V →L[ℝ] ℝ) →L[ℝ] V) ∞
      (fun y => (G y).inverse) e.baseSet :=
    hInv.2.2.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
  have hraised (j : Fin n) : S (raised j) := by
    dsimp only [S]
    rw [e.contMDiffOn_section_baseSet_iff (IB := 𝓡 n) (n := ∞)]
    apply (hIsmooth.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j))).congr
    intro y hy
    dsimp only [raised]
    rw [Trivialization.symmL_apply _ hy]
    exact congrArg Prod.snd (e.apply_mk_symm hy ((G y).inverse (EuclideanSpace.proj j)))
  have hmetric {y : M} (hy : y ∈ e.baseSet) (v w : V) :
      G y v w = g.inner y (e.symmL ℝ y v) (e.symmL ℝ y w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hy hy (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hy v,
      ← Trivialization.symmL_apply (R := ℝ) e hy w]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
  have hpair (j k : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      g.inner y (raised j y) (E k y) = if k = j then 1 else 0 := by
    rw [hframe k hy]
    change g.inner y (e.symmL ℝ y ((G y).inverse (EuclideanSpace.proj j))) _ = _
    rw [← hmetric hy, (hGi hy).self_apply_inverse]
    change (EuclideanSpace.single k (1 : ℝ)) j = if k = j then 1 else 0
    simp only [PiLp.single_apply, eq_comm]
  have hmodel (v : V) : v = ∑ p : Fin n, v p • EuclideanSpace.single p 1 := by
    simpa only [b, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply] using (b.sum_repr v).symm
  have hraisedExpand (k : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      raised k y = ∑ p : Fin n, a y p k • E p y := by
    dsimp only [raised]
    rw [hmodel ((G y).inverse (EuclideanSpace.proj k)), map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, hframe p hy]
  have hthetaRaised (j k : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      theta j y (raised k y) = a y j k := by
    rw [hraisedExpand k hy]
    simp only [map_sum, map_smul, smul_eq_mul, hthetaFrame _ _ hy,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hpairField (j : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ e.baseSet) :
      g.inner y (raised j y) (W y) = theta j y (W y) := by
    have hrec : W y = ∑ p, theta p y (W y) • E p y :=
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
    rw [hrec]
    simp only [map_sum, map_smul, smul_eq_mul, hpair _ _ hy, hthetaFrame _ _ hy]
  intro z hz i j k
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) x :=
    (hW.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hderivPair (p : Fin n) :
      g.inner x (D.connection (raised k) x (E i x)) (E p x) = -Gamma x i p k := by
    have heq : (fun y => g.inner y (raised k y) (E p y)) =ᶠ[𝓝 x]
        (fun _ => if p = k then (1 : ℝ) else 0) :=
      Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) fun y hy => hpair k p hy
    have hzero : mvfderiv (𝓡 n) (fun y => g.inner y (raised k y) (E p y))
        x (E i x) = 0 := by
      calc
        _ = mvfderiv (𝓡 n) (fun _ : M => if p = k then (1 : ℝ) else 0) x (E i x) := by
          dsimp only [mvfderiv]
          rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
          rfl
        _ = 0 := by rw [mvfderiv_const]; rfl
    rw [D.mvfderiv_inner (E i) (raised k) (E p) (hmd _ (hraised k)) (hmd _ (hE p)),
      hpairField k (fun y => D.connection (E p) y (E i y)) hx] at hzero
    change _ + Gamma x i p k = 0 at hzero
    linarith
  have hraisedCov : D.connection (raised k) x (E i x) =
      -(∑ p : Fin n, Gamma x i p k • raised p x) := by
    apply ext_inner_right ℝ
    intro v
    change g.inner x (D.connection (raised k) x (E i x)) v =
      g.inner x (-(∑ p : Fin n, Gamma x i p k • raised p x)) v
    have hv : v = ∑ p : Fin n, (e.basisAt b hx).repr v p • E p x := by
      simpa only [E, e.localFrame_apply_of_mem_baseSet b hx] using
        ((e.basisAt b hx).sum_repr v).symm
    rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [hderivPair p]
    simp [map_neg, map_sum, map_smul, smul_eq_mul, hpair _ _ hx]
  have hcoord := localFrame_covariant_derivative_coordinate D x0 (raised k)
    (hraised k) hx i j
  change theta j x (D.connection (raised k) x (E i x)) =
    mvfderiv (𝓡 n) (fun y => theta j y (raised k y)) x (E i x) +
      ∑ p, Gamma x i p j * theta p x (raised k x) at hcoord
  have heq : (fun y => theta j y (raised k y)) =ᶠ[𝓝 x] (fun y => a y j k) :=
    Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) fun y hy => hthetaRaised j k hy
  have hdcoord : mvfderiv (𝓡 n) (fun y => theta j y (raised k y)) x (E i x) =
      mvfderiv (𝓡 n) (fun y => a y j k) x (E i x) := by
    dsimp only [mvfderiv]
    rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
    rfl
  have ha : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => a y j k) e.baseSet :=
    (contMDiffOn_const (c := EuclideanSpace.proj j)).clm_apply
      (hIsmooth.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj k)))
  have hchart : mvfderiv (𝓡 n) (fun y => a y j k) x (E i x) =
      fderiv ℝ (fun w => a (c.symm w) j k) z (EuclideanSpace.single i 1) := by
    have hc : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have ht : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hfd : fderiv ℝ (fun w => a (c.symm w) j k) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) (fun y => a y j k) x
          (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) ((fun y => a y j k) ∘ c.symm) z
        (EuclideanSpace.single i 1) = _
      have hfa : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => a y j k) (c.symm z) :=
        (ha.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [mvfderiv_comp_apply z hfa hc (EuclideanSpace.single i 1), ← ht]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) (fun y => a y j k) x) (hframe i hx)).trans hfd.symm
  rw [hraisedCov, map_neg, map_sum] at hcoord
  simp only [map_smul, smul_eq_mul, hthetaRaised _ _ hx, hdcoord, hchart] at hcoord
  change fderiv ℝ (fun w => a (c.symm w) j k) z (EuclideanSpace.single i 1) = _
  rw [Finset.sum_add_distrib]
  linarith


theorem metric_inverse_eq_sum_orthonormal_coordinates
    (g : RiemannianMetric n M) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let theta := e.localFrameCoeff (𝓡 n) b
    let G := fun y : M =>
      ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
        (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
        x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
    ∀ x ∈ e.baseSet, ∀ i j : Fin n,
      a x i j = ∑ r, theta i x ((g.orthonormalBasis x) r) *
        theta j x ((g.orthonormalBasis x) r) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M =>
    ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G y) (EuclideanSpace.proj j)) i
  intro x hx i j
  change a x i j = _
  have htheta (p : Fin n) (v : TangentSpace (𝓡 n) x) :
      theta p x v = (e.continuousLinearMapAt ℝ x v) p := by
    have hh := e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) b hx
      (FiberBundle.extend V v) p
    rw [FiberBundle.extend_apply_self] at hh
    change theta p x v = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, b, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
    rfl
  have hmetric (v w : V) :
      G x v w = g.inner x (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx v,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
  have hfamily : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) Set.univ :=
    (g.contMDiff.comp contMDiff_snd).contMDiffOn
  have hGi : (G x).IsInvertible :=
    (contMDiffOn_family_metric_frame_inverse hfamily x0).1 (0, x) hx
  let raised := e.symmL ℝ x ((G x).inverse (EuclideanSpace.proj j))
  have hraisedCoord : theta i x raised = a x i j := by
    rw [htheta]
    change (e.continuousLinearMapAt ℝ x
      (e.symmL ℝ x ((G x).inverse (EuclideanSpace.proj j)))) i = _
    rw [Trivialization.continuousLinearMapAt_symmL _ hx]
  have hpair (v : TangentSpace (𝓡 n) x) :
      g.inner x raised v = theta j x v := by
    calc
      _ = G x ((G x).inverse (EuclideanSpace.proj j))
          (e.continuousLinearMapAt ℝ x v) := by
        rw [hmetric, Trivialization.symmL_continuousLinearMapAt _ hx]
      _ = (e.continuousLinearMapAt ℝ x v) j := by
        rw [hGi.self_apply_inverse]
        rfl
      _ = _ := (htheta j v).symm
  let o := g.orthonormalBasis x
  have hsum : (∑ r, g.inner x (o r) raised * theta i x (o r)) = theta i x raised := by
    have hh := o.sum_repr' raised
    change (∑ r, g.inner x (o r) raised • o r) = raised at hh
    simpa only [map_sum, map_smul, smul_eq_mul] using
      congrArg (theta i x) hh
  calc
    a x i j = theta i x raised := hraisedCoord.symm
    _ = ∑ r, g.inner x (o r) raised * theta i x (o r) := hsum.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [g.symm x (o r) raised, hpair (o r)]
      exact mul_comm _ _

set_option maxHeartbeats 3600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_derivative_metric_rate_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (v : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let W := fun α β : Fin 4 → Fin n => ∏ r, a (α r) (β r)
    let raised := fun i => e.symmL ℝ x (G.inverse (EuclideanSpace.proj i))
    let q := ∑ α, ∑ β, W α β * g.inner x (v α) (v β);
    -2 * (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) +
      (∑ α, ∑ β, ∑ r : Fin 4, 2 * D.ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) ≤
      (2 * (n : ℝ) + 8 * (n : ℝ) ^ 2) * D.curvatureTensorNorm x * q := by
  classical
  have inputMetricSlotWeight
      {ι κ : Type} [Fintype ι] [Fintype κ]
      (theta : ι → κ → ℝ) (ric : κ → κ → ℝ) (r : Fin 4)
      (α β : Fin 4 → ι) :
      let a := fun i j => ∑ p, theta i p * theta j p
      let d := fun (γ : Fin 4 → κ) (δ : Fin 4 → ι) => ∏ s, theta (δ s) (γ s)
      let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
      (∑ γ : Fin 4 → κ, ∑ p : κ,
        ric p (γ r) * d γ α * d (Function.update γ r p) β) =
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * h (α r) (β r) := by
    classical
    let a := fun i j => ∑ p, theta i p * theta j p
    let d := fun (γ : Fin 4 → κ) (δ : Fin 4 → ι) => ∏ s, theta (δ s) (γ s)
    let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
    let rest := fun γ : Fin 4 → κ =>
      ∏ s ∈ Finset.univ.erase r, theta (α s) (γ s) * theta (β s) (γ s)
    let weight := ∏ s ∈ Finset.univ.erase r, a (α s) (β s)
    have hd (γ : Fin 4 → κ) (δ : Fin 4 → ι) :
        d γ δ = theta (δ r) (γ r) *
          ∏ s ∈ Finset.univ.erase r, theta (δ s) (γ s) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ r)).symm
    have hterm (γ : Fin 4 → κ) (p : κ) :
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
        (∑ γ : Fin 4 → κ, c (γ r) * rest γ) = (∑ p, c p) * weight := by
      let f := fun (s : Fin 4) (i : κ) =>
        if s = r then c i else theta (α s) i * theta (β s) i
      have hf (γ : Fin 4 → κ) :
          (∏ s, f s (γ s)) = c (γ r) * rest γ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
        simp only [f, ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro s hs
        rw [if_neg (Finset.mem_erase.mp hs).1]
      have hfs : (∏ s : Fin 4, ∑ i : κ, f s i) = (∑ i, c i) * weight := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
        simp only [f, ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro s hs
        simp only [if_neg (Finset.mem_erase.mp hs).1]
        rfl
      calc
        _ = ∑ γ : Fin 4 → κ, ∏ s, f s (γ s) := by simp only [hf]
        _ = ∏ s : Fin 4, ∑ i : κ, f s i := (Fintype.prod_sum f).symm
        _ = _ := hfs
    change (∑ γ : Fin 4 → κ, ∑ p : κ,
        ric p (γ r) * d γ α * d (Function.update γ r p) β) = weight * h (α r) (β r)
    calc
      _ = ∑ p : κ, ∑ γ : Fin 4 → κ,
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
      (theta : ι → κ → ℝ) (ric : κ → κ → ℝ) (r : Fin 4)
      (v : (Fin 4 → ι) → Z) :
      let a := fun i j => ∑ p, theta i p * theta j p
      let d := fun (γ : Fin 4 → κ) (δ : Fin 4 → ι) => ∏ s, theta (δ s) (γ s)
      let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
      let V := fun γ => ∑ α, d γ α • v α
      (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        h (α r) (β r) * B (v α) (v β)) =
        ∑ γ : Fin 4 → κ, ∑ p : κ,
          ric p (γ r) * B (V γ) (V (Function.update γ r p)) := by
    classical
    let a := fun i j => ∑ p, theta i p * theta j p
    let d := fun (γ : Fin 4 → κ) (δ : Fin 4 → ι) => ∏ s, theta (δ s) (γ s)
    let h := fun i j => ∑ p, ∑ q, ric p q * theta i q * theta j p
    let V := fun γ => ∑ α, d γ α • v α
    have hweight (α β : Fin 4 → ι) :
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * h (α r) (β r) =
          ∑ γ : Fin 4 → κ, ∑ p : κ,
            ric p (γ r) * d γ α * d (Function.update γ r p) β :=
      (inputMetricSlotWeight theta ric r α β).symm
    have hswap (f : (Fin 4 → ι) → (Fin 4 → ι) → (Fin 4 → κ) → κ → ℝ) :
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
        ∑ γ : Fin 4 → κ, ∑ p : κ,
          ric p (γ r) * B (V γ) (V (Function.update γ r p))
    calc
      _ = ∑ α, ∑ β, (∑ γ : Fin 4 → κ, ∑ p : κ,
          ric p (γ r) * d γ α * d (Function.update γ r p) β) * B (v α) (v β) := by
        simp only [hweight]
      _ = ∑ γ : Fin 4 → κ, ∑ p : κ, ∑ α, ∑ β,
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
  let W := fun α β : Fin 4 → Fin n => ∏ r, a (α r) (β r)
  let raised := fun i => e.symmL ℝ x (G.inverse (EuclideanSpace.proj i))
  let q := ∑ α, ∑ β, W α β * g.inner x (v α) (v β)
  let A := D.curvatureTensorNorm x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let d := fun (γ : Fin 4 → ι) (α : Fin 4 → Fin n) =>
    ∏ r, theta (α r) x (b (γ r))
  let z := fun γ : Fin 4 → ι => ∑ α, d γ α • v α
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
  have hWeight (α β : Fin 4 → Fin n) :
      W α β = ∑ γ : Fin 4 → ι, d γ α * d γ β := by
    dsimp only [W]
    simp_rw [htrace]
    rw [Fintype.prod_sum]
    simp only [d, Finset.prod_mul_distrib]
    rfl
  have hfull (B : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
      (∑ γ, B (z γ) (z γ)) = ∑ α, ∑ β, W α β * B (v α) (v β) := by
    have hex (γ : Fin 4 → ι) : B (z γ) (z γ) =
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
  have hinput (r : Fin 4) :
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
  have hslot (r : Fin 4) :
      (∑ γ, ∑ p, ‖z γ‖ * ‖z (Function.update γ r p)‖) ≤ (n : ℝ) * q := by
    let swap := fun s : (Fin 4 → ι) × ι => (Function.update s.1 r s.2, s.1 r)
    have hs : Function.Involutive swap := by
      intro s
      apply Prod.ext
      · funext j
        by_cases hj : j = r
        · subst j
          simp [swap]
        · simp [swap, Function.update_of_ne hj]
      · simp [swap]
    let eqv : ((Fin 4 → ι) × ι) ≃ ((Fin 4 → ι) × ι) :=
      { toFun := swap, invFun := swap, left_inv := hs, right_inv := hs }
    have hswap : (∑ γ, ∑ p, ‖z (Function.update γ r p)‖ ^ 2) =
        ∑ γ, ∑ _p : ι, ‖z γ‖ ^ 2 := by
      have hh := eqv.sum_comp (fun s => ‖z s.1‖ ^ 2)
      change (∑ s : (Fin 4 → ι) × ι, ‖z (Function.update s.1 r s.2)‖ ^ 2) =
        ∑ s : (Fin 4 → ι) × ι, ‖z s.1‖ ^ 2 at hh
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
  have hinputBound (r : Fin 4) :
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
  have hall : (∑ α, ∑ β, ∑ r : Fin 4,
      2 * D.ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) =
      ∑ r : Fin 4, 2 * (∑ α, ∑ β, (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β)) := by
    calc
      _ = ∑ α, ∑ r : Fin 4, ∑ β,
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
  have hallBound : (∑ r : Fin 4, 2 * (∑ α, ∑ β,
      (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) *
        D.ricci x (raised (β r)) (raised (α r)) * g.inner x (v α) (v β))) ≤
      8 * (n : ℝ) ^ 2 * A * q := by
    calc
      _ ≤ ∑ _r : Fin 4, 2 * ((n : ℝ) ^ 2 * A * q) :=
        Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hinputBound r) (by norm_num)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  change -2 * (∑ α, ∑ β, W α β * D.ricci x (v α) (v β)) +
    (∑ α, ∑ β, ∑ r : Fin 4, 2 * D.ricci x (raised (β r)) (raised (α r)) *
      (∏ s ∈ Finset.univ.erase r, a (α s) (β s)) * g.inner x (v α) (v β)) ≤
    (2 * (n : ℝ) + 8 * (n : ℝ) ^ 2) * A * q
  rw [hall]
  nlinarith only [houtputBound, hallBound]


theorem curvature_all_rank_gram_contraction
    {σ ι κ V : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : V →L[ℝ] V →L[ℝ] ℝ)
    (a : ι → ι → ℝ) (c : κ → ι → ℝ)
    (ha : ∀ i j, a i j = ∑ p, c p i * c p j)
    (K L : (σ → ι) → V) :
    (∑ α : σ → ι, ∑ β : σ → ι,
      (∏ s, a (α s) (β s)) * G (K α) (L β)) =
      ∑ γ : σ → κ,
        G (∑ α : σ → ι, (∏ s, c (γ s) (α s)) • K α)
          (∑ β : σ → ι, (∏ s, c (γ s) (β s)) • L β) := by
  classical
  let coeff : (σ → κ) → (σ → ι) → ℝ := fun γ α => ∏ s, c (γ s) (α s)
  have hweight (α β : σ → ι) :
      (∏ s, a (α s) (β s)) = ∑ γ : σ → κ, coeff γ α * coeff γ β := by
    simp_rw [ha]
    simpa only [coeff, Finset.prod_mul_distrib] using
      (Fintype.prod_sum (fun (s : σ) (p : κ) => c p (α s) * c p (β s)))
  have hex (γ : σ → κ) :
      G (∑ α : σ → ι, coeff γ α • K α) (∑ β : σ → ι, coeff γ β • L β) =
        ∑ α : σ → ι, ∑ β : σ → ι,
          (coeff γ α * coeff γ β) * G (K α) (L β) := by
    simp only [map_sum, map_smul, sum_apply, smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    ring
  calc
    _ = ∑ α : σ → ι, ∑ β : σ → ι,
        (∑ γ : σ → κ, coeff γ α * coeff γ β) * G (K α) (L β) := by
      simp only [hweight]
    _ = ∑ γ : σ → κ, ∑ α : σ → ι, ∑ β : σ → ι,
        (coeff γ α * coeff γ β) * G (K α) (L β) := by
      symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β _
      exact (Finset.sum_mul ..).symm
    _ = _ := Finset.sum_congr rfl fun γ _ => (hex γ).symm

end PoincareConjecture.Proofs.M03
