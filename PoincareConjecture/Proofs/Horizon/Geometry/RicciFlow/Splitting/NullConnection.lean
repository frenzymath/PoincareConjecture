import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.NullSectionEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Contractions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.DerivativeOnFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.BoundaryRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantRiemannDerivative_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hsec : D.NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, D.ricci y (V y) (V y) = 0)
    (hDV : ∀ a, D.ricci x (D.connection V x a) (D.connection V x a) = 0)
    (a u w z : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, V x, u, w, z] = 0 := by
  let W : Fin 4 → (y : M) → TangentSpace (𝓡 n) y :=
    ![V, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z]
  have hW (i : Fin 4) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (W i)) x := by
    fin_cases i
    · exact hV.mdifferentiableAt (by simp)
    all_goals exact FiberBundle.mdifferentiableAt_extend (𝓡 n) _ _
  have h := D.covariantTensorDerivative_on_fields hD.1 W x hW a
  have heq : (fun y => D.riemannEvaluation y (fun i => W i y)) =ᶠ[𝓝 x]
      fun _ => 0 := by
    filter_upwards [hnull] with y hy
    exact curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD y (hsec y) hy _ _ _
  have hsum : (∑ i, D.riemannEvaluation x
      (Function.update (fun j => W j x) i (D.connection (W i) x a))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    fin_cases i
    · simpa [W, LeviCivitaData.riemannEvaluation] using
        curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD x (hsec x) (hDV a) u w z
    all_goals
      simpa [W, LeviCivitaData.riemannEvaluation] using
        curvatureTensor_eq_zero_of_ricci_self_eq_zero D hD x (hsec x)
          hnull.self_of_nhds _ _ _
  have hvalues : Fin.cons a (fun i => W i x) = ![a, V x, u, w, z] := by
    ext i
    fin_cases i <;> simp [W]
  rw [hvalues, Poincare.mvfderiv_eq_of_eventuallyEq heq, mvfderiv_const, hsum] at h
  simpa only [zero_apply, sub_zero] using h

theorem covariantRicciDerivative_all_slots_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hsec : D.NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, D.ricci y (V y) (V y) = 0)
    (hDV : ∀ a, D.ricci x (D.connection V x a) (D.connection V x a) = 0)
    (a w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![a, V x, w] = 0 ∧
      D.covariantTensorDerivative D.ricciEvaluation x ![a, w, V x] = 0 ∧
      D.covariantTensorDerivative D.ricciEvaluation x ![V x, a, w] = 0 := by
  have hRic (y : M) (u : TangentSpace (𝓡 n) y) : 0 ≤ D.ricci y u u :=
    Finset.sum_nonneg fun i _ => hsec y u (g.orthonormalBasis y i)
  have hn : ∀ᶠ y in 𝓝 x, ∀ z, D.ricci y (V y) z = 0 := by
    filter_upwards [hnull] with y hy
    exact ricci_eq_zero_of_nonneg_of_self_eq_zero D hD y (hRic y) hy
  have hslot (c d : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative D.ricciEvaluation x ![c, V x, d] = 0 := by
    rw [covariantRicciDerivative_on_null_section D hD V hV hn,
      ricci_eq_zero_of_nonneg_of_self_eq_zero D hD x (hRic x) (hDV c), neg_zero]
  refine ⟨hslot a w, ?_, ?_⟩
  · rw [D.covariantTensorDerivative_ricciEvaluation_symm hD]
    exact hslot a w
  · have hB := D.sum_covariantTensorDerivative_riemannEvaluation_divergence hD x a (V x) w
    have hzero (i) : D.covariantTensorDerivative D.riemannEvaluation x
        ![g.orthonormalBasis x i, a, g.orthonormalBasis x i, w, V x] = 0 := by
      rw [D.covariantTensorDerivative_riemannEvaluation_pair_swap hD,
        D.covariantTensorDerivative_riemannEvaluation_skew_first hD,
        covariantRiemannDerivative_null_section D hD hsec V hV hnull hDV, neg_zero]
    simp only [hzero, Finset.sum_const_zero] at hB
    rw [D.covariantTensorDerivative_ricciEvaluation_symm hD x w a (V x), hslot] at hB
    linarith

theorem covariantRicciDerivative_all_slots_eq_zero_of_terminal_null
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, (F.connection b).ricci y (V y) (V y) = 0)
    (u w : TangentSpace (𝓡 n) x) :
    (F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation
        x ![u, V x, w] = 0 ∧
      (F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation
        x ![u, w, V x] = 0 ∧
      (F.connection b).covariantTensorDerivative (F.connection b).ricciEvaluation
        x ![V x, u, w] = 0 := by
  apply covariantRicciDerivative_all_slots_null_section (F.connection b)
    (hC.tensor_calculus n M (F.metric b) (F.connection b))
    (hsec b ⟨hab.le, le_rfl⟩) V hV hnull
  intro c
  exact ricci_connection_eq_zero_of_terminal_null hC hab F hsec V hV hnull c _

theorem secondCovariantRicciDerivative_eq_zero_of_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, D.ricci y (V y) (V y) = 0)
    (hDV : ∀ a, D.ricci x (D.connection V x a) (D.connection V x a) = 0)
    (hfirst : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace (𝓡 n) y,
      D.ricci y v v = 0 → ∀ a w,
        D.covariantTensorDerivative D.ricciEvaluation y ![a, v, w] = 0)
    (a b w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
      x ![a, b, V x, w] = 0 := by
  let W : Fin 3 → (y : M) → TangentSpace (𝓡 n) y :=
    ![FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b, V,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w]
  have hW (i : Fin 3) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (W i)) x := by
    fin_cases i
    · exact FiberBundle.mdifferentiableAt_extend (𝓡 n) _ _
    · exact hV.mdifferentiableAt (by simp)
    · exact FiberBundle.mdifferentiableAt_extend (𝓡 n) _ _
  have h := D.covariantTensorDerivative_on_fields
    (hD.2.2.1 2 D.ricciEvaluation hD.2.1) W x hW a
  have heq : (fun y => D.covariantTensorDerivative D.ricciEvaluation y
      (fun i => W i y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hnull, hfirst] with y hy hfy
    have htuple : (fun i => W i y) = ![W 0 y, V y, W 2 y] := by
      ext i
      fin_cases i <;> rfl
    rw [htuple]
    exact hfy (V y) hy _ _
  have hu₀ (z : TangentSpace (𝓡 n) x) :
      Function.update (fun j => W j x) 0 z = ![z, V x, w] := by
    ext j
    fin_cases j <;> simp [W]
  have hu₁ (z : TangentSpace (𝓡 n) x) :
      Function.update (fun j => W j x) 1 z = ![b, z, w] := by
    ext j
    fin_cases j <;> simp [W]
  have hu₂ (z : TangentSpace (𝓡 n) x) :
      Function.update (fun j => W j x) 2 z = ![b, V x, z] := by
    ext j
    fin_cases j <;> simp [W]
  have hsum : (∑ i, D.covariantTensorDerivative D.ricciEvaluation x
      (Function.update (fun j => W j x) i (D.connection (W i) x a))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    fin_cases i
    · change D.covariantTensorDerivative D.ricciEvaluation x
        (Function.update (fun j => W j x) 0 (D.connection (W 0) x a)) = 0
      rw [hu₀]
      exact hfirst.self_of_nhds (V x) hnull.self_of_nhds _ w
    · change D.covariantTensorDerivative D.ricciEvaluation x
        (Function.update (fun j => W j x) 1 (D.connection (W 1) x a)) = 0
      rw [hu₁]
      exact hfirst.self_of_nhds (D.connection V x a) (hDV a) b w
    · change D.covariantTensorDerivative D.ricciEvaluation x
        (Function.update (fun j => W j x) 2 (D.connection (W 2) x a)) = 0
      rw [hu₂]
      exact hfirst.self_of_nhds (V x) hnull.self_of_nhds b _
  have hvalues : Fin.cons a (fun i => W i x) = ![a, b, V x, w] := by
    ext i
    fin_cases i <;> simp [W]
  rw [hvalues, Poincare.mvfderiv_eq_of_eventuallyEq heq, mvfderiv_const, hsum] at h
  simpa only [zero_apply, sub_zero] using h

theorem connection_hasDerivAt_zero_of_covariantRicciDerivative_eq_zero
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hzero : ∀ u w : TangentSpace (𝓡 n) x,
      (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![u, V x, w] = 0 ∧
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![u, w, V x] = 0 ∧
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![V x, u, w] = 0) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => (F.connection s).connection V x) 0 t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (V x)
  have hW := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (V x)
  obtain ⟨A, hA, hpair⟩ := F.connection_hasDerivAt_ricci_of_equation ht x (V x)
  have hAzero : A = 0 := by
    ext u
    apply ext_inner_right ℝ
    intro w
    change (F.metric t).inner x (A u) w = (F.metric t).inner x 0 w
    rw [hpair, (hzero u w).1, (hzero u w).2.2, (hzero w u).2.1]
    simp
  have heq (s : ℝ) : (F.connection s).connection V x =
      (F.connection s).connection W x +
        ((F.connection t).connection V x - (F.connection t).connection W x) := by
    have hd := (F.connection s).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp)
      (hV.mdifferentiableAt (by simp))
    have hw := (F.connection s).connection.isCovariantDerivativeOnUniv.difference_apply
      (F.connection t).connection.isCovariantDerivativeOnUniv (by simp) hW
    simp only [FiberBundle.extend_apply_self] at hw
    have hdiff := hd.symm.trans hw
    change (F.connection s).connection V x - (F.connection t).connection V x =
      (F.connection s).connection W x - (F.connection t).connection W x at hdiff
    rw [sub_eq_iff_eq_add] at hdiff
    rw [hdiff]
    abel
  rw [hAzero] at hA
  exact (hA.add_const ((F.connection t).connection V x -
    (F.connection t).connection W x)).congr_of_eventuallyEq (Eventually.of_forall heq)

theorem connection_eq_terminal_of_ricci_null
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y)
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hnull : ∀ t ∈ Ioc a b, ∀ x, (F.connection t).ricci x (V x) (V x) = 0) :
    ∀ t ∈ Icc a b, ∀ x, (F.connection t).connection V x =
      (F.connection b).connection V x := by
  intro t ht x
  ext u
  let v := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let e := v.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt _ _ x)
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun s => e ((F.connection s).connection V x u)
  have hc : ContinuousOn q (Icc a b) := by
    intro s hs
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    exact e.continuous.continuousAt.comp_continuousWithinAt
      (((F.contDiffWithinAt_connection hs (hV x)).clm_apply
        (contDiffWithinAt_const (c := u))).continuousWithinAt)
  have hd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt q 0 s := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2.le
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub
      ordConnected_Icc ⟨a, left_mem_Icc.mpr hs.1.le, s, right_mem_Icc.mpr hs.1.le, hs.1.ne⟩
    have hz := covariantRicciDerivative_all_slots_eq_zero_of_terminal_null hC hs.1 G
      (fun r hr => hsec r (hsub hr)) V (hV x)
      (Eventually.of_forall (hnull s ⟨hs.1, hs.2.le⟩))
    have hh := connection_hasDerivAt_zero_of_covariantRicciDerivative_eq_zero F
      (by simpa only [interior_Icc] using hs) V (hV x) hz
    have hv := hh.clm_apply (hasDerivAt_const s u)
    convert! e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hv using 1
    simp
  let c := (a + b) / 2
  have hc₀ : c ∈ Ioo a b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have heq : EqOn q (fun _ => q c) (Ioo a b) := by
    intro s hs
    have hbound := (convex_Ioo a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hd r hr).hasDerivWithinAt) (fun r hr => le_refl ‖(0 : EuclideanSpace ℝ (Fin n))‖)
      hc₀ hs
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  have hclosed : EqOn q (fun _ => q c) (Icc a b) :=
    heq.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  apply e.injective
  exact (hclosed ht).trans (hclosed ⟨hab.le, le_rfl⟩).symm

end PoincareConjecture.RicciFlow.Splitting
