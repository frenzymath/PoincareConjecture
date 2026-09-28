import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciNormEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Norm







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

section LocalIsometry

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem LeviCivitaData.ricciNormSq_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hD' : D'.CurvatureTensorCalculus)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) : D.ricciNormSq x = D'.ricciNormSq (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  obtain ⟨A, hA⟩ := hD'.2.1.1 (f x)
  have hinv := multilinear_sum_sq_comp_linearIsometryEquiv A e'
    (g.orthonormalBasis x) (h.orthonormalBasis (f x))
  have hs {ι : Type} [Fintype ι] (v : ι → TangentSpace (𝓡 n) (f x)) :
      (∑ a : Fin 2 → ι, (A (fun i => v (a i))) ^ 2) =
        ∑ i, ∑ j, (D'.ricci (f x) (v i) (v j)) ^ 2 := by
    rw [Fintype.sum_equiv (finTwoArrowEquiv ι)
      (fun a => (A (fun i => v (a i))) ^ 2)
      (fun p => (D'.ricci (f x) (v p.1) (v p.2)) ^ 2) (fun a => ?_),
      Fintype.sum_prod_type]
    rw [← hA]
    rfl
  rw [hs (fun i => e' (g.orthonormalBasis x i)), hs (h.orthonormalBasis (f x))] at hinv
  change D.ricciNormSq x = _
  rw [LeviCivitaData.ricciNormSq]
  simp_rw [D.ricci_eq_of_local_isometry D' hU hf hmetric hx]
  exact hinv

end LocalIsometry

section Scaling

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private def linearSquarePairing {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => L u * L v)
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_left_comm])

theorem rescaledMetric_ricciNormSq (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).ricciNormSq x = c⁻¹ ^ 2 * D.ricciNormSq x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  let B := bilinearOfTwoTensor A
  have hB (u v : TangentSpace (𝓡 n) x) : B u v = D.ricci x u v := by
    exact (hA ![u,v]).symm
  let b := g.orthonormalBasis x
  let e := (rescaledMetric g c hc).orthonormalBasis x
  have hrow (u : TangentSpace (𝓡 n) x) :
      (∑ i, (B u (e i)) ^ 2) = c⁻¹ * ∑ i, (B u (b i)) ^ 2 := by
    simpa only [linearSquarePairing, LinearMap.mk₂_apply, ← pow_two] using
      rescaledMetric_bilinear_trace g c hc x (linearSquarePairing (B u))
  have hcol (v : TangentSpace (𝓡 n) x) :
      (∑ i, (B (e i) v) ^ 2) = c⁻¹ * ∑ i, (B (b i) v) ^ 2 := by
    simpa only [linearSquarePairing, LinearMap.mk₂_apply, LinearMap.flip_apply,
      ← pow_two] using
      rescaledMetric_bilinear_trace g c hc x (linearSquarePairing (B.flip v))
  simp only [LeviCivitaData.ricciNormSq, rescaledMetric_ricci, ← hB]
  change (∑ i, ∑ j, (B (e i) (e j)) ^ 2) = c⁻¹ ^ 2 * ∑ i, ∑ j, (B (b i) (b j)) ^ 2
  simp_rw [hrow, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hcol, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

end Scaling

section Homothety

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g h : RiemannianMetric n M} {c : ℝ}

theorem HomotheticMetricSlice.ricciNormSq (hC : RicciFlowCurvatureTheory.{u})
    (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.ricciNormSq x = c⁻¹ ^ 2 * D.ricciNormSq (E.map x) := by
  rw [← rescaledMetric_ricciNormSq g D (hC.tensor_calculus n M g D) c hc]
  exact D'.ricciNormSq_eq_of_local_isometry
    (rescaledMetric_connection g D c hc)
    (hC.tensor_calculus n M (rescaledMetric g c hc) (rescaledMetric_connection g D c hc))
    isOpen_univ E.map.contMDiff.contMDiffOn
    (fun y _ u v => E.inner_eq y u v) (Set.mem_univ x)


theorem HomotheticMetricSlice.normalizedRicciNormSq (hC : RicciFlowCurvatureTheory.{u})
    (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M) :
    D'.ricciNormSq x / D'.scalarCurvature x ^ 2 =
      D.ricciNormSq (E.map x) / D.scalarCurvature (E.map x) ^ 2 := by
  rw [E.ricciNormSq hC hc D D', E.scalarCurvature hc D D', mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hc.ne'))]

theorem HomotheticMetricSlice.ricci_pos
    (E : HomotheticMetricSlice g h c) (hc : 0 < c)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, v ≠ 0 → 0 < D.ricci x v v)
    (x : M) (v : TangentSpace (𝓡 n) x) (hv : v ≠ 0) : 0 < D'.ricci x v v := by
  have hinj := h.mfderiv_bijective_of_pullback_eq (rescaledMetric g c hc) x
    (fun a b => (E.inner_eq x a b).symm)
  have hv' : mfderiv (𝓡 n) (𝓡 n) E.map x v ≠ 0 := by
    intro hz
    apply hv
    apply hinj.1
    exact hz.trans (map_zero _).symm
  rw [D'.ricci_eq_of_local_isometry (rescaledMetric_connection g D c hc)
    isOpen_univ E.map.contMDiff.contMDiffOn (fun y _ a b => E.inner_eq y a b)
    (Set.mem_univ x), rescaledMetric_ricci]
  exact hRic _ _ hv'

end Homothety

section ShrinkingFlow

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData n M}

theorem ShrinkingSolitonFlow.scalarCurvature_pos_at_time
    (G : ShrinkingSolitonFlow S) (hR : ∀ x : M, 0 < S.connection.scalarCurvature x)
    {t : ℝ} (ht : t < 0) (x : M) : 0 < (G.flow.connection t).scalarCurvature x := by
  obtain ⟨E⟩ := G.self_similar t ht
  rw [E.scalarCurvature (abs_pos.mpr ht.ne) S.connection (G.flow.connection t)]
  exact mul_pos (inv_pos.mpr (abs_pos.mpr ht.ne)) (hR _)



theorem ShrinkingSolitonFlow.exists_stationary_normalizedRicciNormSq_max
    [CompactSpace M] (hC : RicciFlowCurvatureTheory.{u}) (G : ShrinkingSolitonFlow S)
    (hR : ∀ x : M, 0 < S.connection.scalarCurvature x) {t : ℝ} (ht : t < 0) :
    ∃ x : M,
      (∀ s : ℝ, s < 0 → ∀ y : M,
        (G.flow.connection s).ricciNormSq y / (G.flow.connection s).scalarCurvature y ^ 2 ≤
          (G.flow.connection t).ricciNormSq x / (G.flow.connection t).scalarCurvature x ^ 2) ∧
      deriv (fun s => (G.flow.connection s).ricciNormSq x /
        (G.flow.connection s).scalarCurvature x ^ 2) t = 0 := by
  let q := fun y => S.connection.ricciNormSq y / S.connection.scalarCurvature y ^ 2
  have hD := hC.tensor_calculus n M S.metric S.connection
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q :=
    (RicciFlow.contMDiff_ricciNormSq S.connection hD).div₀
      (hD.contMDiff_scalarCurvature.pow 2) (fun y => pow_ne_zero _ (hR y).ne')
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hq.continuous.continuousOn
  obtain ⟨E⟩ := G.self_similar t ht
  let x := E.map.symm p
  have hx : (G.flow.connection t).ricciNormSq x /
      (G.flow.connection t).scalarCurvature x ^ 2 = q p := by
    rw [E.normalizedRicciNormSq hC (abs_pos.mpr ht.ne) S.connection (G.flow.connection t)]
    simp only [x, Diffeomorph.apply_symm_apply]
    rfl
  have hmax (s : ℝ) (hs : s < 0) (y : M) :
      (G.flow.connection s).ricciNormSq y / (G.flow.connection s).scalarCurvature y ^ 2 ≤
        (G.flow.connection t).ricciNormSq x / (G.flow.connection t).scalarCurvature x ^ 2 := by
    obtain ⟨E'⟩ := G.self_similar s hs
    rw [hx, E'.normalizedRicciNormSq hC (abs_pos.mpr hs.ne) S.connection (G.flow.connection s)]
    exact hp (Set.mem_univ (E'.map y))
  refine ⟨x, hmax, ?_⟩
  apply IsLocalMax.deriv_eq_zero
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  exact hmax s hs x

end ShrinkingFlow

end PoincareConjecture
