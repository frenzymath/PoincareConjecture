import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderFlow
import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)




theorem endCylinderFlow_chart_coefficients :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ), t ∈ Ico 0 1 → ∀ (p : endReferenceRegion e) (x : StandardCapSpace),
      x ∈ endReferenceRegion e →
      (((endCylinderFlow e).metric t).pullbackCoefficients
        (extChartAt (𝓡 3) p).symm) x = endCylinderCoefficients e t x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t ht p x hx
  rw [RiemannianMetric.pullbackCoefficients_canonicalChart (endReferenceRegion e)
    (endReferenceRegion_isOpen e) _ p ⟨x, hx⟩]
  ext u v
  change (endCylinderMetric e t).inner ⟨x, hx⟩ u v = endCylinderCoefficients e t x u v
  rw [endCylinderMetric_inner, endCylinderParameter, if_pos ht]




theorem endCylinderFlow_iteratedFDeriv :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ (t : ℝ), t ∈ Ico 0 1 → ∀ (p : endReferenceRegion e) (j : ℕ) (x : StandardCapSpace),
      x ∈ endReferenceRegion e →
      iteratedFDeriv ℝ j (((endCylinderFlow e).metric t).pullbackCoefficients
        (extChartAt (𝓡 3) p).symm) x = iteratedFDeriv ℝ j (endCylinderCoefficients e t) x := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t ht p j x hx
  have heq : ((endCylinderFlow e).metric t).pullbackCoefficients
      (extChartAt (𝓡 3) p).symm =ᶠ[𝓝 x] endCylinderCoefficients e t := by
    filter_upwards [(endReferenceRegion_isOpen e).mem_nhds hx] with y hy
    exact endCylinderFlow_chart_coefficients e t ht p y hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds




theorem endCylinderFlow_compact_bounds {T : ℝ} (hT : T < 1)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∃ a M : ℝ, 0 < a ∧ 1 ≤ M ∧ ∀ t ∈ Icc 0 T,
      ∀ (p : endReferenceRegion e) (x : StandardCapSpace), x ∈ K → x ∈ endReferenceRegion e →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j (((endCylinderFlow e).metric t).pullbackCoefficients
          (extChartAt (𝓡 3) p).symm) x‖ ≤ M) ∧
        (∀ v : StandardCapSpace, a * ‖v‖ ^ 2 ≤
          ((endCylinderFlow e).metric t).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm x v v) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  have htI {t : ℝ} (ht : t ∈ Icc 0 T) : t ∈ Ico 0 1 := ⟨ht.1, ht.2.trans_lt hT⟩
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨a, ha, hell⟩ := exists_uniform_bilinear_family_lower_bound hcompact
    (endCylinderCoefficients_contDiff e).continuous.continuousOn
    (fun z hz v hv => endCylinderCoefficients_pos e (htI hz.1) z.2 v hv)
  have hbound (j : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (endCylinderCoefficients e t) x‖ ≤ C := by
    have hc : ContinuousOn
        (fun z : ℝ × StandardCapSpace => iteratedFDeriv ℝ j (endCylinderCoefficients e z.1) z.2)
        (Icc 0 T ×ˢ K) :=
      ((endCylinderCoefficients_contDiff e).contDiffOn.iteratedFDeriv_snd_of_isOpen
        (U := univ) (S := univ) isOpen_univ j).continuousOn.mono
          (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
    exact ⟨max C 1, le_max_right _ _, fun t ht x hx =>
      (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)⟩
  choose C hC hb using hbound
  let M := ∑ j ∈ Finset.range (m + 1), C j
  have hCM (j : ℕ) (hj : j ≤ m) : C j ≤ M :=
    Finset.single_le_sum (fun i _ => zero_le_one.trans (hC i)) (by simpa using hj)
  refine ⟨a, M, ha, (hC 0).trans (hCM 0 (Nat.zero_le m)), ?_⟩
  intro t ht p x hx hxU
  constructor
  · intro j hj
    rw [endCylinderFlow_iteratedFDeriv e t (htI ht) p j x hxU]
    exact (hb j t ht x hx).trans (hCM j hj)
  · intro v
    rw [endCylinderFlow_chart_coefficients e t (htI ht) p x hxU]
    exact hell (t, x) ⟨ht, hx⟩ v

end PoincareConjecture.M34
