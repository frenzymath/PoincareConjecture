import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.ExteriorInitialScalar
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapChapter11Geometry
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryBoxScalar
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPoint
import PoincareConjecture.Proofs.M34.Mathlib.GuardedQuadraticGrowth
import PoincareConjecture.Proofs.M34.Standard.NonnegativeCurvatureNorm
import PoincareConjecture.Proofs.M04.ScalarEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

theorem partialFlow_exists_exterior_scalar_bound_of_good_points
    {g0 : StandardInitialMetric} (F : PartialStandardCapFlow g0)
    (P : M34StandardCapPredecessors) (E0 : StandardCapEstimate g0)
    (R : OrdinaryProductRicciGeometry F.flow.metric (partialFlowSpacetimeInterval F))
    {epsilon C A Rstar : ℝ} (hA : 0 < A) (hL : F.lifetime < 1)
    (hgood : ∀ p : (ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F)
      (F := F.flow) R).point,
      Rstar ≤ (ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F)
        (F := F.flow) R).scalar p →
      Chapter11GoodPoint (ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F)
        (F := F.flow) R) epsilon C A p) :
    ∃ B : ℝ, 0 < B ∧ Rstar ≤ B ∧ ∃ T0 ∈ Ioo 0 F.lifetime,
      ∃ X : Set StandardCapSpace, IsCompact X ∧
        ∀ t ∈ Ico T0 F.lifetime, ∀ x ∉ X,
          0 ≤ (F.flow.connection t).scalarCurvature x ∧
          (F.flow.connection t).scalarCurvature x ≤ 2 * B ∧
          (F.flow.connection t).curvatureTensorNorm x ≤ 2 * B := by
  let G := ordinaryChapter11Flow (I := partialFlowSpacetimeInterval F) (F := F.flow) R
  obtain ⟨K, _hK, hinit⟩ := partialFlow_exists_exterior_initial_scalar_bound P.curvature E0 F hL
  let B := max 1 (max Rstar (9 * K))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRB : Rstar ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : 9 * K ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let delta := min (F.lifetime / 2) (1 / (16 * A * B))
  have hden : 0 < 16 * A * B := by positivity
  have hdelta : 0 < delta := lt_min (half_pos F.lifetime_pos) (div_pos zero_lt_one hden)
  have hhalf : delta ≤ F.lifetime / 2 := min_le_left _ _
  have hsmall : delta * (16 * A * B) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  let T0 := F.lifetime - delta
  have hT0 : T0 ∈ Ioo 0 F.lifetime := by
    dsimp [T0]
    constructor <;> linarith [F.lifetime_pos]
  have htime : 4 * A * B * (F.lifetime - T0) < 1 := by
    dsimp [T0]
    nlinarith
  obtain ⟨X, hX, hXbound⟩ := hinit T0 hT0
  refine ⟨B, hB, hRB, T0, hT0, X, hX, ?_⟩
  intro t ht x hx
  let f : ℝ → ℝ := fun s => (F.flow.connection s).scalarCurvature x
  have hsub : Icc T0 t ⊆ Ico 0 F.lifetime :=
    fun s hs => ⟨hT0.1.le.trans hs.1, hs.2.trans_lt ht.2⟩
  have hsubo : Ioo T0 t ⊆ Ico 0 F.lifetime :=
    fun _ hs => hsub ⟨hs.1.le, hs.2.le⟩
  have hc : ContinuousOn f (Icc T0 t) :=
    (F.flow.contDiffOn_scalarCurvature_timeSlice x).continuousOn.mono hsub
  have hd : DifferentiableOn ℝ f (Ioo T0 t) :=
    ((F.flow.contDiffOn_scalarCurvature_timeSlice x).differentiableOn (by simp)).mono hsubo
  have hguard : ∀ s ∈ Ioo T0 t, Rstar ≤ f s → deriv f s ≤ A * (f s) ^ 2 := by
    intro s hs hhigh
    have hsincl := hsubo hs
    let b : G.box_index := ⟨()⟩
    let p : G.point := ⟨s, (G.box b).forward s hsincl x⟩
    have he := ordinaryChapter11_box_scalar_eq (I := partialFlowSpacetimeInterval F)
      (F := F.flow) R (partialFlow_chapter11_calculus F P R) b hsincl x
    have hp : Rstar ≤ G.scalar p := hhigh.trans_eq he.symm
    obtain ⟨d, hderiv, hbound⟩ := (hgood p hp).scalar_time_derivative b hsincl x rfl
    change HasDerivWithinAt f d (Ico 0 F.lifetime) s at hderiv
    have hn : Ico 0 F.lifetime ∈ 𝓝 s := Filter.mem_of_superset
      (isOpen_Ioo.mem_nhds ⟨hT0.1.trans hs.1, hs.2.trans ht.2⟩) Ioo_subset_Ico_self
    calc
      deriv f s = d := (hderiv.hasDerivAt hn).deriv
      _ ≤ |d| := le_abs_self _
      _ ≤ A * (f s) ^ 2 := hbound
  have htime' : 4 * A * B * (t - T0) < 1 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le T0) (by positivity)).trans_lt htime
  have hscalar : (F.flow.connection t).scalarCurvature x < 2 * B :=
    hc.lt_two_mul_of_guarded_quadratic_deriv hd hA.le hB hRB
      (((le_abs_self _).trans (hXbound x hx)).trans hKB) hguard htime' t ⟨ht.1, le_rfl⟩
  have hnorm := (F.flow.connection t).curvatureTensorNorm_le_scalar_of_nonnegative_sectional x
    (partialFlow_nonnegativeSectionalCurvature P.curvature E0 F t
      ⟨hT0.1.le.trans ht.1, ht.2⟩ x)
  have hnonneg : 0 ≤ (F.flow.connection t).curvatureTensorNorm x := Real.sqrt_nonneg _
  exact ⟨hnonneg.trans hnorm, hscalar.le, hnorm.trans hscalar.le⟩

end PoincareConjecture.M34
