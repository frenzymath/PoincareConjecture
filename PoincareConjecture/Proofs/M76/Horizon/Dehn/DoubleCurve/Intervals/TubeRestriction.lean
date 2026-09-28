import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation










set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I01" => Icc (0 : ℝ) 1


noncomputable def tubeTransverseContraction (ε : ℝ) : C3 →ᴬ[ℝ] C3 :=
  let xy := ContinuousLinearMap.fst ℝ P2 ℝ
  let t := ContinuousLinearMap.snd ℝ P2 ℝ
  ((ε • xy).prod t).toContinuousAffineMap

theorem tubeTransverseContraction_apply (ε : ℝ) (z : C3) :
    tubeTransverseContraction ε z = ((ε * z.1.1, ε * z.1.2), z.2) := rfl


theorem tubeTransverseContraction_mapsTo {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MapsTo (tubeTransverseContraction ε) tube tube := by
  rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
  change ((ε * x ∈ Icc (-1 : ℝ) 1) ∧ ε * y ∈ Icc (-1 : ℝ) 1) ∧ t ∈ Icc 0 1
  exact ⟨⟨⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩,
    ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩⟩, ht⟩

theorem tubeTransverseContraction_axis (ε t : ℝ) :
    tubeTransverseContraction ε ((0, 0), t) = ((0, 0), t) := by
  simp [tubeTransverseContraction_apply]


theorem tubeTransverseContraction_injective {ε : ℝ} (hε : ε ≠ 0) :
    Function.Injective (tubeTransverseContraction ε) := by
  intro x y h
  have h1 := congrArg (fun z : C3 ↦ z.1.1) h
  have h2 := congrArg (fun z : C3 ↦ z.1.2) h
  have ht := congrArg (fun z : C3 ↦ z.2) h
  apply Prod.ext
  · exact Prod.ext (mul_left_cancel₀ hε h1) (mul_left_cancel₀ hε h2)
  · exact ht


theorem tubeTransverseContraction_diagonal_iff {ε : ℝ} (hε : ε ≠ 0)
    (j : Fin 2) (z : C3) :
    (tubeTransverseContraction ε z).1.2 =
      (if j = 0 then (tubeTransverseContraction ε z).1.1
        else -(tubeTransverseContraction ε z).1.1) ↔
      z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
  rw [tubeTransverseContraction_apply]
  split_ifs <;> simp only [← mul_neg]
  all_goals exact ⟨mul_left_cancel₀ hε, fun h ↦ congrArg (fun x ↦ ε * x) h⟩


theorem tubeTransverseContraction_finitePL (ε : ℝ) :
    FinitePiecewiseAffineOn (tubeTransverseContraction ε) tube := by
  have hbox := ((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (tubeTransverseContraction ε)⟩


theorem exists_tube_transverse_contraction_into_open
    {X : Type*} [TopologicalSpace X] {τ : C3 → X}
    (hτ : ContinuousOn τ tube) {O : Set X} (hO : IsOpen O)
    (haxis : ∀ t : I01, τ ((0, 0), t) ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ MapsTo (τ ∘ tubeTransverseContraction ε) tube O := by
  have htube : IsCompact tube := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have : CompactSpace tube := isCompact_iff_compactSpace.mp htube
  let c : I01 × tube → tube := fun p ↦ ⟨tubeTransverseContraction p.1 p.2,
    tubeTransverseContraction_mapsTo p.1.property.1 p.1.property.2 p.2.property⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    change Continuous (fun p : I01 × tube ↦
      (((p.1 : ℝ) * (p.2 : C3).1.1, (p.1 : ℝ) * (p.2 : C3).1.2), (p.2 : C3).2))
    fun_prop
  have htc : Continuous (fun p : I01 × tube ↦ τ (c p)) := hτ.domRestrict.comp hc
  have hzero : ({0} : Set I01) ×ˢ (univ : Set tube) ⊆
      (fun p : I01 × tube ↦ τ (c p)) ⁻¹' O := by
    rintro ⟨s, z⟩ ⟨hs, _⟩
    have hs0 : s = 0 := hs
    subst s
    change τ (tubeTransverseContraction 0 z) ∈ O
    simpa only [tubeTransverseContraction_apply, zero_mul] using
      haxis ⟨(z : C3).2, z.property.2⟩
  obtain ⟨U, V, hU, _, h0U, hUV, hprod⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ (hO.preimage htc) hzero
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (mem_singleton 0))
  let ε : ℝ := min (δ / 2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεU : (⟨ε, hε.le, hε1⟩ : I01) ∈ U := by
    apply hδU
    change dist ε 0 < δ
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεδ
  refine ⟨ε, hε, hε1, ?_⟩
  intro z hz
  exact hprod (show (⟨ε, hε.le, hε1⟩, ⟨z, hz⟩) ∈ U ×ˢ V from
    ⟨hεU, hUV (mem_univ (⟨z, hz⟩ : tube))⟩)


theorem contracted_tube_polyhedralPL
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X F} {τ : C3 → X}
    (hτ : PolyhedralPLInCharts e τ tube) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    PolyhedralPLInCharts e (τ ∘ tubeTransverseContraction ε) tube := by
  obtain ⟨K, hK, hKs, hAff⟩ := tubeTransverseContraction_finitePL ε
  have h := hτ.comp_finitePiecewiseAffineOn K hK
    (show FinitePiecewiseAffineOn (tubeTransverseContraction ε) K.space from
      ⟨K, hK, rfl, hAff⟩)
    (fun z hz ↦ tubeTransverseContraction_mapsTo hε hε1 (hKs.subset hz))
  exact hKs ▸ h


theorem contracted_tube_finitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {sigma : C3 → E} (hσ : FinitePiecewiseAffineOn sigma tube)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    FinitePiecewiseAffineOn (sigma ∘ tubeTransverseContraction ε) tube :=
  hσ.comp (tubeTransverseContraction_finitePL ε) (tubeTransverseContraction_mapsTo hε hε1)



theorem exists_restricted_PL_tube
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X F} {τ : C3 → X}
    (hτ : PolyhedralPLInCharts e τ tube) (hi : InjOn τ tube)
    {O Z : Set X} (hO : IsOpen O) (haxis : ∀ t : I01, τ ((0, 0), t) ∈ O)
    (hends : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      MapsTo (τ ∘ tubeTransverseContraction ε) tube O ∧
      PolyhedralPLInCharts e (τ ∘ tubeTransverseContraction ε) tube ∧
      InjOn (τ ∘ tubeTransverseContraction ε) tube ∧
      (∀ t : ℝ, (τ ∘ tubeTransverseContraction ε) ((0, 0), t) = τ ((0, 0), t)) ∧
      ∀ z ∈ tube, (τ ∘ tubeTransverseContraction ε) z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1 := by
  obtain ⟨ε, hε, hε1, hmap⟩ := exists_tube_transverse_contraction_into_open
    hτ.continuousOn hO haxis
  have hc := tubeTransverseContraction_mapsTo hε.le hε1
  refine ⟨ε, hε, hε1, hmap, contracted_tube_polyhedralPL hτ hε.le hε1, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact tubeTransverseContraction_injective hε.ne' (hi (hc hx) (hc hy) hxy)
  · intro t
    simp only [Function.comp_apply, tubeTransverseContraction_axis]
  · intro z hz
    exact hends _ (hc hz)

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
