import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Restriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.TubeRestriction



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

noncomputable def stripTransverseContraction (r : ℝ) : P2 →ᴬ[ℝ] P2 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (r • ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap

private theorem strip_contraction_mapsTo {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    MapsTo (stripTransverseContraction r) source source := by
  intro p hp
  exact ⟨hp.1, ⟨by change -1 ≤ r * p.2; nlinarith [hp.2.1],
    by change r * p.2 ≤ 1; nlinarith [hp.2.2]⟩⟩

private theorem strip_contraction_finitePL (r : ℝ) :
    FinitePiecewiseAffineOn (stripTransverseContraction r) source := by
  have h := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := h
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (stripTransverseContraction r)⟩

private theorem strip_contraction_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective (stripTransverseContraction r) := by
  intro p q h
  have h₁ := congrArg (fun z : P2 => z.1) h
  have h₂ := congrArg (fun z : P2 => z.2) h
  change p.1 = q.1 at h₁
  change r * p.2 = r * q.2 at h₂
  exact Prod.ext h₁ (mul_left_cancel₀ hr.ne' h₂)

private theorem strip_contraction_sheet (r : ℝ) (b : Bool) (p : P2) :
    originalStripSheet b (stripTransverseContraction r p) =
      tubeTransverseContraction r (originalStripSheet b p) := by
  cases b <;> simp [originalStripSheet, stripTransverseContraction, tubeTransverseContraction_apply]

theorem tubeTransverseContraction_image_closedTube {r : ℝ} (hr : 0 < r) :
    tubeTransverseContraction r '' tube = closedTube r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨⟨by change -r ≤ r * z.1.1; nlinarith [hz.1.1.1],
      by change r * z.1.1 ≤ r; nlinarith [hz.1.1.2]⟩,
      ⟨by change -r ≤ r * z.1.2; nlinarith [hz.1.2.1],
      by change r * z.1.2 ≤ r; nlinarith [hz.1.2.2]⟩⟩, hz.2⟩
  · intro z hz
    refine ⟨((z.1.1 / r, z.1.2 / r), z.2), ?_, ?_⟩
    · refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hz.2⟩
      · exact (le_div_iff₀ hr).mpr (by simpa using hz.1.1.1)
      · exact (div_le_iff₀ hr).mpr (by simpa using hz.1.1.2)
      · exact (le_div_iff₀ hr).mpr (by simpa using hz.1.2.1)
      · exact (div_le_iff₀ hr).mpr (by simpa using hz.1.2.2)
    · simp only [tubeTransverseContraction_apply, mul_div_cancel₀ _ hr.ne']

theorem tubeTransverseContraction_image_openTube {r : ℝ} (hr : 0 < r) :
    tubeTransverseContraction r '' openTube 1 = openTube r := by
  have hopen (s : ℝ) (z : C3) : z ∈ openTube s ↔
      ((-s < z.1.1 ∧ z.1.1 < s) ∧ (-s < z.1.2 ∧ z.1.2 < s)) ∧
        z.2 ∈ Icc 0 1 := by
    simp only [openTube, transverseSquare, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo]
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [hopen] at hz ⊢
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hz.2⟩
    · change -r < r * z.1.1
      nlinarith [hz.1.1.1]
    · change r * z.1.1 < r
      nlinarith [hz.1.1.2]
    · change -r < r * z.1.2
      nlinarith [hz.1.2.1]
    · change r * z.1.2 < r
      nlinarith [hz.1.2.2]
  · intro z hz
    rw [hopen] at hz
    refine ⟨((z.1.1 / r, z.1.2 / r), z.2), ?_, ?_⟩
    · rw [hopen]
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hz.2⟩
      · exact (lt_div_iff₀ hr).mpr (by simpa using hz.1.1.1)
      · exact (div_lt_iff₀ hr).mpr (by simpa using hz.1.1.2)
      · exact (lt_div_iff₀ hr).mpr (by simpa using hz.1.2.1)
      · exact (div_lt_iff₀ hr).mpr (by simpa using hz.1.2.2)
    · simp only [tubeTransverseContraction_apply, mul_div_cancel₀ _ hr.ne']

private theorem strip_contraction_arm (r : ℝ) :
    stripTransverseContraction r '' arm 0 = arm 0 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, by change r * q.2 = 0; rw [show q.2 = 0 from hq.2, mul_zero]⟩
  · intro hp
    refine ⟨p, hp, Prod.ext rfl ?_⟩
    change r * p.2 = p.2
    rw [show p.2 = 0 from hp.2, mul_zero]

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

private theorem rescaled_strip_preimage
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (b : Bool) (V : Set P2) (f : P2 → X) (c : P2 → P2)
    (hc : MapsTo c source V)
    (hsheet : ∀ p ∈ source, f (c p) = U.map (originalStripSheet b p))
    (hpre : V ∩ f ⁻¹' (U.map '' tube) = c '' source) :
    V ∩ f ⁻¹' ((U.map ∘ tubeTransverseContraction r) '' tube) =
      (c ∘ stripTransverseContraction r) '' source := by
  have hm := tubeTransverseContraction_mapsTo hr.le hr1
  ext x
  constructor
  · rintro ⟨hx, z, hz, hzv⟩
    obtain ⟨p, hp, rfl⟩ := hpre.subset ⟨hx, tubeTransverseContraction r z, hm hz, hzv⟩
    have heq : originalStripSheet b p = tubeTransverseContraction r z :=
      congrArg Subtype.val (U.embedding.injective
        (a₁ := ⟨_, originalStripSheet_mem_tube b hp⟩) (a₂ := ⟨_, hm hz⟩)
        ((hsheet p hp).symm.trans hzv.symm))
    have hp2 : p.2 = r * z.1.1 := by
      simpa only [originalStripSheet, tubeTransverseContraction_apply] using congrArg (fun w : C3 => w.1.1) heq
    refine ⟨(p.1, z.1.1), ⟨hp.1, hz.1.1⟩, ?_⟩
    exact congrArg c (Prod.ext rfl hp2.symm)
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hc (strip_contraction_mapsTo hr hr1 hp), originalStripSheet b p,
      originalStripSheet_mem_tube b hp, ?_⟩
    change U.map (tubeTransverseContraction r (originalStripSheet b p)) =
      f (c (stripTransverseContraction r p))
    rw [hsheet _ (strip_contraction_mapsTo hr hr1 hp), strip_contraction_sheet]

theorem OriginalIntervalTube.exists_rescaling
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ V : OriginalIntervalTube e R W S T C D f₀ f₁,
      V.map = U.map ∘ tubeTransverseContraction r ∧
      V.first = U.first ∘ stripTransverseContraction r ∧
      V.second = U.second ∘ stripTransverseContraction r ∧
      V.map '' tube = U.map '' closedTube r := by
  let sc := stripTransverseContraction r
  let tc := tubeTransverseContraction r
  have hsmap := strip_contraction_mapsTo hr hr1
  have htmap := tubeTransverseContraction_mapsTo hr.le hr1
  let : CompactSpace source := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  let : CompactSpace tube := isCompact_iff_compactSpace.mp
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  have hse : IsEmbedding (fun p : source => (⟨sc p, hsmap p.property⟩ : source)) :=
    (((sc.continuous.comp continuous_subtype_val).subtype_mk _).isClosedEmbedding
      (fun p q h => Subtype.ext (strip_contraction_injective hr (congrArg Subtype.val h)))).isEmbedding
  have hte : IsEmbedding (fun p : tube => (⟨tc p, htmap p.property⟩ : tube)) :=
    (((tc.continuous.comp continuous_subtype_val).subtype_mk _).isClosedEmbedding
      (fun p q h => Subtype.ext (tubeTransverseContraction_injective hr.ne'
        (congrArg Subtype.val h)))).isEmbedding
  let V : OriginalIntervalTube e R W S T C D f₀ f₁ := {
    first := U.first ∘ sc
    second := U.second ∘ sc
    map := U.map ∘ tc
    first_pl := U.first_pl.comp (strip_contraction_finitePL r) hsmap
    second_pl := U.second_pl.comp (strip_contraction_finitePL r) hsmap
    first_embedding := U.first_embedding.comp hse
    second_embedding := U.second_embedding.comp hse
    first_mapsTo := U.first_mapsTo.comp hsmap
    second_mapsTo := U.second_mapsTo.comp hsmap
    pl := contracted_tube_polyhedralPL U.pl hr.le hr1
    embedding := U.embedding.comp hte
    mapsTo_region := U.mapsTo_region.comp htmap
    mapsTo_neighborhood := U.mapsTo_neighborhood.comp htmap
    first_sheet := fun p hp => (U.first_sheet _ (hsmap hp)).trans
      (congrArg U.map (strip_contraction_sheet r false p))
    second_sheet := fun p hp => (U.second_sheet _ (hsmap hp)).trans
      (congrArg U.map (strip_contraction_sheet r true p))
    first_preimage := rescaled_strip_preimage U hr hr1 false S f₀ U.first
      U.first_mapsTo U.first_sheet U.first_preimage
    second_preimage := rescaled_strip_preimage U hr hr1 true T f₁ U.second
      U.second_mapsTo U.second_sheet U.second_preimage
    first_center := by rw [image_comp, strip_contraction_arm]; exact U.first_center
    second_center := by rw [image_comp, strip_contraction_arm]; exact U.second_center
    first_trace := fun z hz => (U.first_trace _ (htmap hz)).trans
      ⟨mul_left_cancel₀ hr.ne', fun h => congrArg (fun a => r * a) h⟩
    second_trace := fun z hz => (U.second_trace _ (htmap hz)).trans (by
      change r * z.1.2 = -(r * z.1.1) ↔ z.1.2 = -z.1.1
      rw [← mul_neg]
      exact ⟨mul_left_cancel₀ hr.ne', fun h => congrArg (fun a => r * a) h⟩)
    frontier_iff := fun z hz => U.frontier_iff _ (htmap hz) }
  refine ⟨V, rfl, rfl, rfl, ?_⟩
  change (U.map ∘ tubeTransverseContraction r) '' tube = _
  rw [image_comp, tubeTransverseContraction_image_closedTube hr]

theorem OriginalIntervalTube.rescaled_openTube_image
    (U V : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r)
    (hmap : V.map = U.map ∘ tubeTransverseContraction r) :
    V.map '' openTube 1 = U.map '' openTube r := by
  rw [hmap, image_comp, tubeTransverseContraction_image_openTube hr]

theorem OriginalIntervalTube.exists_rescaling_with_open_image
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ V : OriginalIntervalTube e R W S T C D f₀ f₁,
      V.map = U.map ∘ tubeTransverseContraction r ∧
      V.first = U.first ∘ stripTransverseContraction r ∧
      V.second = U.second ∘ stripTransverseContraction r ∧
      V.map '' tube = U.map '' closedTube r ∧
      V.map '' openTube 1 = U.map '' openTube r := by
  obtain ⟨V, hmap, hfirst, hsecond, hclosed⟩ :=
    TubeExterior.OriginalIntervalTube.exists_rescaling U hr hr1
  exact ⟨V, hmap, hfirst, hsecond, hclosed,
    TubeExterior.OriginalIntervalTube.rescaled_openTube_image U V hr hmap⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
