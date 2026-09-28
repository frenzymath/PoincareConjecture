import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Norm








set_option autoImplicit false

open Bundle Manifold Filter Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem normalization_continuousAt_riemannEvaluation_extend (D : LeviCivitaData g) (x : M)
    (v : Fin 4 → TangentSpace (𝓡 n) x) :
    ContinuousAt (fun y => D.riemannEvaluation y
      (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  choose S hS hsmooth using fun i : Fin 4 =>
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (v i)
  have hinter : (⋂ i, S i) ∈ 𝓝 x := Filter.iInter_mem.mpr hS
  obtain ⟨U, hUS, hUopen, hxU⟩ := mem_nhds_iff.mp hinter
  have hsmoothU (i : Fin 4) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i))) U :=
    (hsmooth i).mono (hUS.trans (Set.iInter_subset S i))
  exact (D.riemannEvaluation_smooth hUopen _ hsmoothU).continuousOn.continuousAt
    (hUopen.mem_nhds hxU)


theorem normalization_riemannEvaluation_locally_bounded (D : LeviCivitaData g) (x : M) :
    ∃ B > 0, ∀ᶠ y in 𝓝 x, ∀ v : Fin 4 → TangentSpace (𝓡 n) y,
      |D.riemannEvaluation y v| ≤ B * ∏ i, g.tangentNorm y (v i) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let b := g.orthonormalBasis x
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let L (y : M) : TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) x :=
    (e.symmL ℝ x) ∘L (e.continuousLinearMapAt ℝ y)
  let K (y : M) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) y :=
    (e.symmL ℝ y) ∘L (e.continuousLinearMapAt ℝ x)
  let S (y : M) : ℝ :=
    ∑ p : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      (D.riemannEvaluation y (fun i =>
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b (p i)) y)) ^ 2
  have hS : ContinuousAt S x := by
    dsimp [S]
    apply tendsto_finsetSum
    intro p _
    exact (normalization_continuousAt_riemannEvaluation_extend D x (fun i => b (p i))).pow 2
  let C := Real.sqrt (S x) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hevent : ∀ᶠ y in 𝓝 x, Real.sqrt (S y) < C :=
    hS.sqrt.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  have hL : ∀ᶠ y in 𝓝 x, ‖L y‖ < 2 :=
    eventually_norm_symmL_trivializationAt_self_comp_lt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x one_lt_two
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  refine ⟨16 * C, by positivity, ?_⟩
  filter_upwards [hevent, hL, e.open_baseSet.mem_nhds hx] with y hyC hyL hy
  intro v
  have hKL (w : TangentSpace (𝓡 n) y) : K y (L y w) = w := by
    simp only [K, L, ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_symmL hx, e.symmL_continuousLinearMapAt hy]
  have hK (w : TangentSpace (𝓡 n) x) :
      K y w = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w y := by
    simp only [K, ContinuousLinearMap.comp_apply, FiberBundle.extend]
    rw [e.symmL_apply hy, Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear y
  let A' := A.compLinearMap (fun _ : Fin 4 => (K y).toLinearMap)
  have hbound := normalization_multilinear_sq_le b A' (fun i => L y (v i))
  have heval : A' (fun i => L y (v i)) = D.riemannEvaluation y v := by
    dsimp [A']
    simp only [hKL, ← hA]
  have hcoeff (p : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      A' (fun i => b (p i)) = D.riemannEvaluation y (fun i =>
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b (p i)) y) := by
    dsimp [A']
    simp only [hK, ← hA]
  rw [heval] at hbound
  simp only [hcoeff] at hbound
  change (D.riemannEvaluation y v) ^ 2 ≤ S y * ∏ i, ‖L y (v i)‖ ^ 2 at hbound
  have hSn : 0 ≤ S y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSC : S y ≤ C ^ 2 := by
    nlinarith [Real.sq_sqrt hSn, Real.sqrt_nonneg (S y)]
  have hnorm (i : Fin 4) : ‖L y (v i)‖ ≤ 2 * ‖v i‖ :=
    ((L y).le_opNorm (v i)).trans (mul_le_mul_of_nonneg_right hyL.le (norm_nonneg _))
  have hprod : (∏ i, ‖L y (v i)‖ ^ 2) ≤ 256 * (∏ i, ‖v i‖) ^ 2 := by
    calc
      (∏ i, ‖L y (v i)‖ ^ 2) ≤ ∏ i, (2 * ‖v i‖) ^ 2 := by
        apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
        intro i _
        gcongr
        exact hnorm i
      _ = 256 * (∏ i, ‖v i‖) ^ 2 := by
        norm_num [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow]
  have hnormeq (i : Fin 4) : g.tangentNorm y (v i) = ‖v i‖ := by
    exact (norm_eq_sqrt_real_inner (v i)).symm
  simp only [hnormeq]
  apply le_of_sq_le_sq _ (by positivity)
  rw [sq_abs]
  calc
    (D.riemannEvaluation y v) ^ 2 ≤ S y * ∏ i, ‖L y (v i)‖ ^ 2 := hbound
    _ ≤ C ^ 2 * (256 * (∏ i, ‖v i‖) ^ 2) :=
      mul_le_mul hSC hprod (Finset.prod_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    _ = (16 * C * ∏ i, ‖v i‖) ^ 2 := by ring

theorem normalization_riemannEvaluation_uniform_bound [CompactSpace M] (D : LeviCivitaData g) :
    ∃ B > 0, ∀ x : M, ∀ v : Fin 4 → TangentSpace (𝓡 n) x,
      |D.riemannEvaluation x v| ≤ B * ∏ i, g.tangentNorm x (v i) := by
  classical
  choose C hC hbound using normalization_riemannEvaluation_locally_bounded D
  choose U hUsub hUopen hUmem using fun x => mem_nhds_iff.mp (hbound x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hUmem x⟩)
  have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  refine ⟨1 + ∑ x ∈ s, C x, by linarith, ?_⟩
  intro x v
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have hle : C y ≤ 1 + ∑ z ∈ s, C z := by
    have := Finset.single_le_sum (fun z _ => (hC z).le) hy
    linarith
  exact (hUsub y hxy v).trans (mul_le_mul_of_nonneg_right hle
    (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)))

end PoincareConjecture
