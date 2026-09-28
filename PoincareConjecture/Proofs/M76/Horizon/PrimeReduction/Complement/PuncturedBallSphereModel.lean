import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedPuncturedDoubleSphere

set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_punctured_ball_sphere_model
    {ι : Type*} [Finite ι] {B S : Set E} (hB : IsFinitePLBallPair V3 B S)
    (a r : ι → Set E) (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haB : ∀ i, a i ⊆ B \ S)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) :
    ∃ (f : E → Fin 4 → ℝ) (H : B ≃ₜ lower), H.IsFinitePL ∧
      (∀ x : B, (H x : Fin 4 → ℝ) = f x) ∧
      (∀ x : B, (x : E) ∈ S ↔ (H x : Fin 4 → ℝ) ∈ seam) ∧
      (∀ i, IsFinitePLBallPair V3 (f '' a i) (f '' r i)) ∧
      (∀ i, f '' a i ⊆ lower \ seam) ∧
      (∀ i, Disjoint upper (f '' a i)) ∧
      Pairwise (fun i j => Disjoint (f '' a i) (f '' a j)) ∧
      let p := B \ ⋃ i, a i \ r i
      let P := sphere \ ((upper \ seam) ∪ ⋃ i, (f '' a i) \ (f '' r i))
      ∃ (L : SimplicialComplex ℝ E) (F : p ≃ₜ P),
        L.faces.Finite ∧ L.space = p ∧ F.IsFinitePL ∧
        (∀ x : p, (F x : Fin 4 → ℝ) = f x) ∧
        (∀ i (x : p), (x : E) ∈ r i ↔ (F x : Fin 4 → ℝ) ∈ f '' r i) ∧
        (∀ i, (fun x : p => (F x : Fin 4 → ℝ)) ''
          ((Subtype.val : p → E) ⁻¹' r i) = f '' r i) ∧
        ((fun x : p => (F x : Fin 4 → ℝ)) ''
          ((Subtype.val : p → E) ⁻¹' S) = seam) := by
  obtain ⟨H, hH, hHS⟩ := hB.exists_homeomorph lower_ball
  have hHcopy := hH
  obtain ⟨f, hf, hval⟩ := hHcopy
  have hfi : InjOn f B := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hmarked (c : Set E) (hc : c ⊆ B) (x : B) :
      (x : E) ∈ c ↔ (H x : Fin 4 → ℝ) ∈ f '' c := by
    rw [hval]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hfi (hc hy) x.property hyx ▸ hy
  have hballs (i : ι) := (ha i).image_of_subset hf
    ((haB i).trans sdiff_subset) hfi
  have hhole (i : ι) : f '' a i ⊆ lower \ seam := by
    rintro y ⟨x, hx, rfl⟩
    have hfx := hval ⟨x, (haB i hx).1⟩
    refine ⟨hfx ▸ (H ⟨x, (haB i hx).1⟩).property, ?_⟩
    intro hs
    exact (haB i hx).2 ((hHS ⟨x, (haB i hx).1⟩).mpr (hfx.symm ▸ hs))
  have houterdis (i : ι) : Disjoint upper (f '' a i) := by
    apply disjoint_left.mpr
    intro x hxu hxa
    have hx := hhole i hxa
    exact hx.2 (lower_inter_upper ▸ And.intro hx.1 hxu)
  have hdisImages : Pairwise fun i j => Disjoint (f '' a i) (f '' a j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hfi (haB i hx).1 (haB j hz).1 (hxy.trans hzy.symm)
    exact disjoint_left.mp (hdis hij) hx (hxz.symm ▸ hz)
  have hopen : IsOpen ((Subtype.val : B → E) ⁻¹' (⋃ i, a i \ r i)) := by
    rw [preimage_iUnion]
    exact isOpen_iUnion fun i =>
      hB.isOpen_nested_ball_rim_complement (ha i) ((haB i).trans sdiff_subset)
  have himage : (Subtype.val : B → E) ''
      (((Subtype.val : B → E) ⁻¹' (⋃ i, a i \ r i))ᶜ) =
        B \ ⋃ i, a i \ r i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hclosed : IsClosed (B \ ⋃ i, a i \ r i) := by
    rw [← himage]
    exact hB.isCompact.isClosed.isClosedMap_subtype_val _ hopen.isClosed_compl
  obtain ⟨K, hK, hKs, _⟩ := hf
  obtain ⟨_, L, _, _, _, _, _, hL, hLs, _, _⟩ :=
    K.exists_finite_closed_punctured_ball_carrier hK a r ha
      (fun i => (haB i).trans (sdiff_subset.trans hKs.symm.subset)) hdis
      (hKs.symm ▸ hclosed)
  have hLspace : L.space = B \ ⋃ i, a i \ r i := by
    simpa only [hKs] using hLs
  let p := B \ ⋃ i, a i \ r i
  let P := lower \ ⋃ i, (f '' a i) \ (f '' r i)
  have hp : p ⊆ B := sdiff_subset
  have hP : P ⊆ lower := sdiff_subset
  have hrp (i : ι) : r i ⊆ p := by
    intro x hx
    refine ⟨(haB i ((ha i).1 hx)).1, ?_⟩
    intro hholes
    obtain ⟨j, hxj, hxr⟩ := mem_iUnion.mp hholes
    by_cases hij : i = j
    · exact hxr (hij ▸ hx)
    · exact disjoint_left.mp (hdis hij) ((ha i).1 hx) hxj
  have hSp : S ⊆ p := by
    intro x hx
    refine ⟨hB.1 hx, ?_⟩
    intro hholes
    obtain ⟨i, hxi, _⟩ := mem_iUnion.mp hholes
    exact (haB i hxi).2 hx
  have hpuncture (x : B) : (x : E) ∈ p ↔ (H x : Fin 4 → ℝ) ∈ P := by
    have hholes : (x : E) ∈ ⋃ i, a i \ r i ↔
        (H x : Fin 4 → ℝ) ∈ ⋃ i, (f '' a i) \ (f '' r i) := by
      simp only [mem_iUnion, mem_sdiff,
        ← hmarked (a _) ((haB _).trans sdiff_subset),
        ← hmarked (r _) ((ha _).1.trans ((haB _).trans sdiff_subset))]
    simp only [p, P, mem_sdiff, x.property, (H x).property, true_and, hholes]
  let F := H.restrictSubsets hp hP hpuncture
  have houter : (fun x : p => (F x : Fin 4 → ℝ)) ''
      ((Subtype.val : p → E) ⁻¹' S) = seam := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hHS ⟨x, hp x.property⟩).mp hx
    · intro y hy
      let x := H.symm ⟨y, lower_ball.1 hy⟩
      have hxS : (x : E) ∈ S := (hHS x).mpr (by simp [x, hy])
      refine ⟨⟨x, hSp hxS⟩, hxS, ?_⟩
      exact congrArg Subtype.val (H.apply_symm_apply ⟨y, lower_ball.1 hy⟩)
  have hcarrier : sphere \ ((upper \ seam) ∪ ⋃ i, (f '' a i) \ (f '' r i)) = P := by
    have hbase : sphere \ (upper \ seam) = lower := by
      rw [← lower_union_upper, ← lower_inter_upper]
      ext x
      simp only [mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [← sdiff_sdiff, hbase]
  refine ⟨f, H, hH, hval, hHS, hballs, hhole, houterdis, hdisImages, ?_⟩
  dsimp only
  rw [hcarrier]
  refine ⟨L, F, hL, hLspace, hH.restrictSubsets hp hP hpuncture L hL hLspace,
    fun x => hval ⟨x, hp x.property⟩, ?_, ?_, houter⟩
  · intro i x
    exact hmarked (r i) ((ha i).1.trans ((haB i).trans sdiff_subset)) ⟨x, hp x.property⟩
  · intro i
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmarked (r i) ((ha i).1.trans ((haB i).trans sdiff_subset))
        ⟨x, hp x.property⟩).mp hx
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, hrp i hx⟩, hx, hval ⟨x, (hrp i hx).1⟩⟩

end Set
