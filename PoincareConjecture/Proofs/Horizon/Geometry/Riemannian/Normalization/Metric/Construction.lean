import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Connection.Koszul
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.SmoothCutoff
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum













set_option autoImplicit false

open Bornology Bundle Manifold
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem normalization_isVonNBounded_of_posDef {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (q : F →L[ℝ] F →L[ℝ] ℝ)
    (hpos : ∀ v : F, v ≠ 0 → 0 < q v v) : IsVonNBounded ℝ {v : F | q v v < 1} := by
  rcases subsingleton_or_nontrivial F with hs | hn
  · exact Set.Finite.isVonNBounded (𝕜 := ℝ) (Set.toFinite _)
  have hcompact : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : F) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : Continuous fun v : F => q v v := q.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  set c := q v₀ v₀ with hc_def
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hv₀mem
    norm_num at hv₀mem
  have hc : 0 < c := hpos v₀ hv₀ne
  have hcoer : ∀ v : F, c * ‖v‖ ^ 2 ≤ q v v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      set u := ‖v‖⁻¹ • v with hu
      have hmem : u ∈ Metric.sphere (0 : F) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnv]
      have hqu : c ≤ q u u := hv₀min hmem
      have hexp : q v v = ‖v‖ ^ 2 * q u u := by
        rw [hu]
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp
      rw [hexp]
      nlinarith [hqu, sq_nonneg ‖v‖]
  apply IsVonNBounded.subset _
    (NormedSpace.isVonNBounded_ball ℝ F (Real.sqrt (1 / c) + 1))
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv
  rw [Metric.mem_ball, dist_zero_right]
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h2 : ‖v‖ ^ 2 < 1 / c := by
    rw [lt_div_iff₀ hc]
    linarith [mul_comm c (‖v‖ ^ 2)]
  have h3 : ‖v‖ < Real.sqrt (1 / c) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖ ^ 2) by rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
  linarith [Real.sqrt_nonneg (1 / c)]


variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem normalization_exists_local_positive_form [T2Space M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ s : (y : M) → TangentSpace (𝓡 n) y →L[ℝ]
          TangentSpace (𝓡 n) y →L[ℝ] ℝ,
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
          (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y (s y)) U ∧
        ∀ y ∈ U, (∀ v w, s y v w = s y w v) ∧
          (∀ v, v ≠ 0 → 0 < s y v v) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let I := 𝓡 n
  let (y : M) : ContinuousAdd (TangentSpace I y →L[ℝ] ℝ) :=
    inferInstanceAs (ContinuousAdd (E →L[ℝ] ℝ))
  let V : M → Type _ := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hB_apply (v w : E) : B v w = inner ℝ v w := rfl
  set eT := trivializationAt E (TangentSpace I) x with heT
  have hx : x ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let s : (y : M) → V y := fun y =>
    if hy : y ∈ eT.baseSet then
      ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
        ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
          (ContinuousLinearEquiv.refl ℝ ℝ))) B
    else 0
  have hs_apply : ∀ (y : M) (hy : y ∈ eT.baseSet) (v w : TangentSpace I y),
      s y v w = B (eT.continuousLinearEquivAt ℝ y hy v)
        (eT.continuousLinearEquivAt ℝ y hy w) := by
    intro y hy v w
    simp only [s, dif_pos hy]
    rfl
  refine ⟨eT.baseSet, eT.open_baseSet, hx, s, ?_, ?_⟩
  · have hbase : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) V x).baseSet = eT.baseSet := by
      have htriv0 : (trivializationAt ℝ (Bundle.Trivial M ℝ) x) =
          Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
      simp only [hom_trivializationAt_baseSet, ← heT, htriv0,
        Bundle.Trivial.trivialization, Set.inter_univ, Set.inter_self]
    change ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (s y)) eT.baseSet
    rw [← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
    refine (contMDiffOn_const (c := B)).congr ?_
    intro y hy
    rw [hbase] at hy
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    have hy₂ : y ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z => TangentSpace I z →L[ℝ] ℝ) x).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hy, Set.mem_univ y⟩
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt (E →L[ℝ] ℝ)
        (fun z => TangentSpace I z →L[ℝ] ℝ) x) hy₂]
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply, ← heT]
    have htriv : (trivializationAt ℝ (Bundle.Trivial M ℝ) x) =
        Bundle.Trivial.trivialization M ℝ := Bundle.Trivial.eq_trivialization M ℝ _
    simp only [htriv, Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_apply, hs_apply y hy,
      ← Trivialization.symm_continuousLinearEquivAt_eq' eT hy,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  · intro y hy
    refine ⟨fun v w => ?_, fun v hv => ?_⟩
    · rw [hs_apply y hy, hs_apply y hy, hB_apply, hB_apply]
      exact real_inner_comm _ _
    · rw [hs_apply y hy, hB_apply]
      exact real_inner_self_pos.2 (fun h => hv
        ((eT.continuousLinearEquivAt ℝ y hy).injective (by rw [h, map_zero])))

theorem existsRiemannianMetricOfCompact [T2Space M] [CompactSpace M] :
    Nonempty (RiemannianMetric n M) := by
  classical
  choose U hU hxU s hs hpos using (normalization_exists_local_positive_form (n := n) (M := M))
  choose f hf hnonneg hcenter hsupport using
    (fun x : M => normalization_exists_smooth_cutoff (n := n) x (U x) (hU x) (hxU x))
  let V : M → Set M := fun x => {y | 0 < f x y}
  have hV : ∀ x, IsOpen (V x) := fun x =>
    isOpen_lt continuous_const (hf x).continuous
  have hcover : Set.univ ⊆ ⋃ x, V x := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, hcenter y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  let q : (y : M) → TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y →L[ℝ] ℝ :=
    fun y => ∑ x ∈ t, f x y • s x y
  have hterm_nonneg (y : M) (v : TangentSpace (𝓡 n) y) (x : M) :
      0 ≤ f x y * s x y v v := by
    by_cases hfxy : f x y = 0
    · simp [hfxy]
    have hy : y ∈ U x := hsupport x (subset_tsupport _ hfxy)
    by_cases hv : v = 0
    · simp [hv]
    exact mul_nonneg (hnonneg x y) ((hpos x y hy).2 v hv).le
  have hqpos (y : M) (v : TangentSpace (𝓡 n) y) (hv : v ≠ 0) : 0 < q y v v := by
    obtain ⟨x, hxt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    have hy : y ∈ U x := hsupport x (subset_tsupport _ (ne_of_gt hxy))
    change 0 < (∑ x ∈ t, f x y • s x y) v v
    simp only [sum_apply, smul_apply, smul_eq_mul]
    exact Finset.sum_pos' (fun z _ => hterm_nonneg y v z)
      ⟨x, hxt, mul_pos hxy ((hpos x y hy).2 v hv)⟩
  refine ⟨{
    inner := q
    symm := ?_
    pos := hqpos
    isVonNBounded := fun y => normalization_isVonNBounded_of_posDef
      (F := EuclideanSpace ℝ (Fin n)) (q y) (hqpos y)
    contMDiff := ?_
  }⟩
  · intro y v w
    simp only [q, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hfxy : f x y = 0
    · simp [hfxy]
    rw [(hpos x y (hsupport x (subset_tsupport _ hfxy))).1 v w]
  · exact ContMDiff.sum_section (fun x _ =>
      ContMDiffOn.smul_section_of_tsupport (hf x).contMDiffOn
        (hU x) (hsupport x) (hs x))

end PoincareConjecture

namespace PoincareConjecture

variable {n : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]











noncomputable def rescaledMetric (g : RiemannianMetric n N) (c : ℝ) (hc : 0 < c) :
    RiemannianMetric n N where
  inner x := c • g.inner x
  symm x v w := by
    simp only [smul_apply, smul_eq_mul]
    rw [g.symm x v w]
  pos x v hv := by
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    let L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
      (Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) x)
    refine ((g.isVonNBounded x).image L).subset ?_
    intro v hv
    refine ⟨Real.sqrt c • v, ?_, ?_⟩
    · change g.inner x (Real.sqrt c • v) (Real.sqrt c • v) < 1
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, Real.mul_self_sqrt hc.le]
      exact hv
    · change (Real.sqrt c)⁻¹ • (Real.sqrt c • v) = v
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hc), one_smul]
  contMDiff := g.contMDiff.const_smul_section

theorem rescaledMetric_inner (g : RiemannianMetric n N) (c : ℝ) (hc : 0 < c)
    (x : N) (v w : TangentSpace (𝓡 n) x) :
    (rescaledMetric g c hc).inner x v w = c * g.inner x v w := by
  rfl



noncomputable def rescaledMetric_connection (g : RiemannianMetric n N)
    (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c) :
    LeviCivitaData (rescaledMetric g c hc) := by
  refine {
    connection := D.connection
    smooth := D.smooth
    torsion_eq_zero := D.torsion_eq_zero
    metricCompatible := ?_ }
  have hpair {x : N} {σ τ : (y : N) → TangentSpace (𝓡 n) y}
      (hσ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% σ) x)
      (hτ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% τ) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ g.inner y (σ y) (τ y)) x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact hσ.inner_bundle hτ
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X σ τ _hX hσ hτ
  change mvfderiv (𝓡 n) (fun y ↦ c * g.inner y (σ y) (τ y)) x (X x) =
    c * g.inner x (D.connection σ x (X x)) (τ x) +
      c * g.inner x (σ x) (D.connection τ x (X x))
  rw [mvfderiv_fun_mul mdifferentiableAt_const (hpair hσ hτ)]
  have hconst : mvfderiv (𝓡 n) (fun _ : N ↦ c) x = 0 := mvfderiv_const c
  rw [hconst]
  simp only [smul_zero, add_zero]
  change c * (mvfderiv (𝓡 n) (fun y ↦ g.inner y (σ y) (τ y)) x (X x)) = _
  rw [D.normalization_mvfderiv_inner X σ τ hσ hτ, mul_add]

end PoincareConjecture
