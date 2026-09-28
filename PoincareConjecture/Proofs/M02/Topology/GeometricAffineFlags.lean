import PoincareConjecture.Proofs.M02.Topology.AffineSectionPositiveFlags

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators

universe u v w

namespace PoincareConjecture.Proofs.M02.Topology

private theorem evaluation_mem_support_hull
    {V : Type u} [Fintype V]
    {E : Type v} [AddCommGroup E] [Module Real E]
    (p : V → E) (z : V → Real) (hz : z ∈ stdSimplex Real V) :
    (Fintype.linearCombination Real p) z ∈
      convexHull Real (p '' (finiteCoordinateSupport z : Set V)) := by
  classical
  let t := finiteCoordinateSupport z
  have hsum : ∑ v ∈ t, z v = 1 := by
    calc
      ∑ v ∈ t, z v = ∑ v, z v := Finset.sum_subset (Finset.subset_univ t)
        (fun v _ hv => by_contra fun h => hv ((mem_finiteCoordinateSupport z v).mpr h))
      _ = 1 := hz.2
  have heval : ∑ v ∈ t, z v • p v = (Fintype.linearCombination Real p) z := by
    change (∑ v ∈ t, z v • p v) = ∑ v, z v • p v
    apply Finset.sum_subset (Finset.subset_univ t)
    intro v _ hv
    have hzero : z v = 0 := by_contra fun h => hv ((mem_finiteCoordinateSupport z v).mpr h)
    rw [hzero, zero_smul]
  rw [← heval, ← Finset.centerMass_eq_of_sum_1 _ _ hsum]
  exact t.centerMass_mem_convexHull (fun v _ => hz.1 v) (by rw [hsum]; exact zero_lt_one)
    (fun v hv => Set.mem_image_of_mem p hv)

theorem exists_geometric_affine_section_flag
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : E →ᵃ[Real] F) (U : Set (Finset E))
    (hclosed : ∀ s ∈ U, ∀ t : Finset E, t ⊆ s →
      (∃ x ∈ convexHull Real (t : Set E), A x = 0) → t ∈ U)
    (c : U → E)
    (hc : ∀ i : U, A (c i) = 0 ∧
      ∃ w : E → Real, (∀ v ∈ i.val, 0 < w v) ∧
        (∑ v ∈ i.val, w v) = 1 ∧ (∑ v ∈ i.val, w v • v) = c i)
    (s : U) (x : E) (hx : x ∈ convexHull Real (s.val : Set E)) (hAx : A x = 0) :
    ∃ t : Finset U, t.Nonempty ∧
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
      (∀ i ∈ t, i.val ⊆ s.val) ∧ x ∈ convexHull Real (c '' (t : Set U)) := by
  classical
  let L : (s.val → Real) →ₗ[Real] E := Fintype.linearCombination Real Subtype.val
  let B := A.comp L.toAffineMap
  let J := AffineSectionFace B (Finset.univ : Finset s.val)
  let idxFace (i : J) : Finset E := i.val.image Subtype.val
  have hidxsub (i : J) : idxFace i ⊆ s.val := by
    intro v hv
    obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp hv
    exact v'.property
  have hidxmem (i : J) : idxFace i ∈ U := by
    have hz := affineSectionCenter_spec B (Finset.univ : Finset s.val) i
    apply hclosed s s.property (idxFace i) (hidxsub i)
    refine ⟨L (affineSectionCenter B Finset.univ i), ?_, hz.1.2.2⟩
    have h := evaluation_mem_support_hull Subtype.val
      (affineSectionCenter B (Finset.univ : Finset s.val) i) hz.1.1
    change L (affineSectionCenter B (Finset.univ : Finset s.val) i) ∈
      convexHull Real (idxFace i : Set E)
    simpa only [idxFace, L, hz.2, Finset.coe_image] using h
  let idx (i : J) : U := ⟨idxFace i, hidxmem i⟩
  have hidxmono : Monotone idx := by
    intro i j hij
    exact Finset.image_subset_image hij
  choose cw hcw hcwSum hcwVal using fun i : J => (hc (idx i)).2
  let zc (i : J) (v : s.val) : Real := if v ∈ i.val then cw i v.val else 0
  have hzcpos (i : J) (v : s.val) : 0 < zc i v ↔ v ∈ i.val := by
    by_cases hv : v ∈ i.val
    · simp only [zc, if_pos hv, hv, iff_true]
      exact hcw i v (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    · simp only [zc, if_neg hv, hv, lt_self_iff_false]
  have hzc_nonneg (i : J) (v : s.val) : 0 ≤ zc i v := by
    dsimp [zc]
    split_ifs with hv
    · exact (hcw i v (Finset.mem_image.mpr ⟨v, hv, rfl⟩)).le
    · exact le_rfl
  have hzcSum (i : J) : ∑ v : s.val, zc i v = 1 := by
    have hsum : ∑ v ∈ i.val, cw i v.val = 1 := by
      have h := hcwSum i
      change (∑ v ∈ i.val.image Subtype.val, cw i v) = 1 at h
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
      exact h
    calc
      ∑ v : s.val, zc i v = ∑ v ∈ i.val, zc i v :=
        (Finset.sum_subset (Finset.subset_univ i.val)
          (fun v _ hv => by simp only [zc, if_neg hv])).symm
      _ = ∑ v ∈ i.val, cw i v.val :=
        Finset.sum_congr rfl (fun v hv => if_pos hv)
      _ = 1 := hsum
  have hzcVal (i : J) : L (zc i) = c (idx i) := by
    have hval : ∑ v ∈ i.val, cw i v.val • (v : E) = c (idx i) := by
      have h := hcwVal i
      change (∑ v ∈ i.val.image Subtype.val, cw i v • v) = c (idx i) at h
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
      exact h
    change (∑ v : s.val, zc i v • (v : E)) = c (idx i)
    calc
      ∑ v : s.val, zc i v • (v : E) = ∑ v ∈ i.val, zc i v • (v : E) :=
        (Finset.sum_subset (Finset.subset_univ i.val)
          (fun v _ hv => by simp only [zc, if_neg hv, zero_smul])).symm
      _ = ∑ v ∈ i.val, cw i v.val • (v : E) :=
        Finset.sum_congr rfl (fun v hv => by rw [show zc i v = cw i v.val from if_pos hv])
      _ = c (idx i) := hval
  have hzc (i : J) : zc i ∈ affineCoordinateSection B Finset.univ ∧
      finiteCoordinateSupport (zc i) = i.val := by
    refine ⟨⟨⟨hzc_nonneg i, hzcSum i⟩, Finset.subset_univ _, ?_⟩, ?_⟩
    · change A (L (zc i)) = 0
      rw [hzcVal]
      exact (hc (idx i)).1
    · ext v
      rw [mem_finiteCoordinateSupport]
      exact ⟨fun h => (hzcpos i v).mp (lt_of_le_of_ne (hzc_nonneg i v) (Ne.symm h)),
        fun h => ne_of_gt ((hzcpos i v).mpr h)⟩
  obtain ⟨w, hw, hwsum, hwval⟩ := Finset.mem_convexHull'.mp hx
  let z : s.val → Real := fun v => w v.val
  have hzSum : ∑ v : s.val, z v = 1 := by
    rw [Finset.sum_coe_sort]
    exact hwsum
  have hzVal : L z = x := by
    change (∑ v : s.val, w v.val • (v : E)) = x
    exact (Finset.sum_coe_sort s.val (fun v : E => w v • v)).trans hwval
  have hz : z ∈ affineCoordinateSection B Finset.univ :=
    ⟨⟨fun v => hw v v.property, hzSum⟩, Finset.subset_univ _, by
      change A (L z) = 0
      rw [hzVal, hAx]⟩
  obtain ⟨t, ht, hchain, _, hzhull⟩ :=
    exists_affine_section_flag_of_centers B Finset.univ zc hzc z hz
  refine ⟨t.image idx, ht.image idx, ?_, ?_, ?_⟩
  · intro i hi j hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    exact (hchain i' hi' j' hj').imp (fun h => hidxmono h) (fun h => hidxmono h)
  · intro i hi
    obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hi
    exact hidxsub i'
  · have h := Set.mem_image_of_mem L hzhull
    rw [L.image_convexHull, Set.image_image] at h
    rw [← hzVal]
    apply convexHull_mono _ h
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨idx i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, (hzcVal i).symm⟩

theorem mem_range_finiteOrderComplexMap_iff
    {I : Type u} [PartialOrder I] [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E]
    (c : I → E) (x : E) :
    x ∈ Set.range (finiteOrderComplexMap I c) ↔
      ∃ t : Finset I, t.Nonempty ∧
        (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
        x ∈ convexHull Real (c '' (t : Set I)) := by
  classical
  let L : (I → Real) →ₗ[Real] E := Fintype.linearCombination Real c
  let basisPoint : I → I → Real := fun i => Pi.single i 1
  have himage (t : Finset I) : L '' convexHull Real (basisPoint '' (t : Set I)) =
      convexHull Real (c '' (t : Set I)) := by
    rw [L.image_convexHull, Set.image_image]
    congr 1
    have heval : (fun i => L (basisPoint i)) = c := by
      funext i
      simp only [L, basisPoint, Fintype.linearCombination_apply_single, one_smul]
    exact congrArg (fun f : I → E => f '' (t : Set I)) heval
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨f, hf, hzf⟩ := Geometry.SimplicialComplex.mem_space_iff.mp z.property
    obtain ⟨t, ht, hchain, hft⟩ := (finiteOrderComplex_faces I f).mp hf
    refine ⟨t, ht, hchain, ?_⟩
    rw [← himage]
    refine ⟨z.val, ?_, rfl⟩
    simpa only [hft, Finset.coe_image] using hzf
  · rintro ⟨t, ht, hchain, hx⟩
    rw [← himage] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hface : t.image basisPoint ∈ (finiteOrderComplex I).faces := by
      apply (finiteOrderComplex_faces I _).mpr
      refine ⟨t, ht, hchain, ?_⟩
      apply Finset.image_congr
      intro i hi
      funext j
      simp only [basisPoint, Pi.single_apply]
    have hzspace : z ∈ (finiteOrderComplex I).space := by
      apply Geometry.SimplicialComplex.convexHull_subset_space hface
      simpa only [Finset.coe_image] using hz
    exact ⟨⟨z, hzspace⟩, hzx⟩

theorem geometricAffineFlagMap_range
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    {F : Type v} [AddCommGroup F] [Module Real F]
    (A : E →ᵃ[Real] F) (U : Set (Finset E)) [Fintype U]
    (hclosed : ∀ s ∈ U, ∀ t : Finset E, t ⊆ s →
      (∃ x ∈ convexHull Real (t : Set E), A x = 0) → t ∈ U)
    (c : U → E)
    (hc : ∀ i : U, A (c i) = 0 ∧
      ∃ w : E → Real, (∀ v ∈ i.val, 0 < w v) ∧
        (∑ v ∈ i.val, w v) = 1 ∧ (∑ v ∈ i.val, w v • v) = c i) :
    Set.range (finiteOrderComplexMap U c) =
      {x | ∃ s : U, x ∈ convexHull Real (s.val : Set E) ∧ A x = 0} := by
  classical
  ext x
  rw [mem_range_finiteOrderComplexMap_iff]
  constructor
  · rintro ⟨t, ht, hchain, hx⟩
    obtain ⟨s, hs, hsmax⟩ := Finset.exists_maximal ht
    have hsub (i : U) (hi : i ∈ t) : i.val ⊆ s.val := by
      rcases hchain i hi s hs with hle | hle
      · exact hle
      · exact hsmax hi hle
    refine ⟨s, ?_, ?_⟩
    · apply convexHull_min _ (convex_convexHull Real _) hx
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨w, hw, hsum, hval⟩ := (hc i).2
      exact convexHull_mono (hsub i hi)
        (Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩)
    · have hfiber : Convex Real {z : E | A z = 0} :=
        (convex_singleton (0 : F)).affine_preimage A
      apply convexHull_min _ hfiber hx
      rintro _ ⟨i, hi, rfl⟩
      exact (hc i).1
  · rintro ⟨s, hx, hAx⟩
    obtain ⟨t, ht, hchain, _, hx⟩ :=
      exists_geometric_affine_section_flag A U hclosed c hc s x hx hAx
    exact ⟨t, ht, hchain, hx⟩

end PoincareConjecture.Proofs.M02.Topology
