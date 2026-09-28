import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallOuterAttachment
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.attach_original_endpoint_half_strip
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D R S : Set X}
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (HB : N.space ≃ₜ S) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hi : Topology.IsEmbedding
      (fun z : (N.space ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    (hcenter : ∀ z : N.space, c ((z : E), 0) = HB z)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) (side : Bool)
    (ball : ChartwisePLBall e D
      (c '' (N.space ×ˢ {if side then eps else -eps})))
    (hD : D ⊆ R \ c '' (N.space ×ˢ Ioo (-eps) eps))
    (hstrip : c '' (N.space ×ˢ Icc (-eps) eps) ⊆ R) :
    Nonempty (ChartwisePLBall e
      (D ∪ c '' (N.space ×ˢ (if side then Icc 0 eps else Icc (-eps) 0))) S) ∧
      D ⊆ interior
        (D ∪ c '' (N.space ×ˢ (if side then Icc 0 eps else Icc (-eps) 0))) ∧
      D ∪ c '' (N.space ×ˢ (if side then Icc 0 eps else Icc (-eps) 0)) ⊆ R := by
  let a : ℝ := if side then 1 else -1
  have hane : a ≠ 0 := by cases side <;> norm_num [a]
  let A : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (a • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hAval (z : E × ℝ) : A z = (z.1, a * z.2) := rfl
  let v : E × ℝ → X := c ∘ A
  have hAmap : MapsTo A (N.space ×ˢ Icc (0 : ℝ) 1)
      (N.space ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change -1 ≤ a * z.2 ∧ a * z.2 ≤ 1
    cases side <;> simp only [a, Bool.false_eq_true, ↓reduceIte, neg_mul,
      one_mul] <;> constructor <;> linarith [hz.2.1, hz.2.2]
  obtain ⟨K, hK, hKI⟩ := N.exists_finite_interval_product hN
    (by norm_num : (0 : ℝ) < 1)
  have hv : PolyhedralPLInCharts e v (N.space ×ˢ Icc (0 : ℝ) 1) := by
    have h := hc.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK)
      (fun z hz => hAmap (hKI.subset hz))
    exact hKI ▸ h
  have hvinj : InjOn v (N.space ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw heq
    have hAw : A z = A w := congrArg Subtype.val
      (hi.injective (a₁ := ⟨A z, hAmap hz⟩) (a₂ := ⟨A w, hAmap hw⟩) heq)
    have ht := congrArg Prod.snd hAw
    have hfst := congrArg Prod.fst hAw
    change z.1 = w.1 at hfst
    change a * z.2 = a * w.2 at ht
    exact Prod.ext hfst (mul_left_cancel₀ hane ht)
  let T : Set (E × ℝ) := N.space ×ˢ Icc (0 : ℝ) 1
  let : CompactSpace T := isCompact_iff_compactSpace.mp
    ((N.isCompact_space_of_finite hN).prod isCompact_Icc)
  let H : T ≃ₜ v '' T := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn v T hvinj) (hv.continuousOn.domRestrict.subtype_mk _)
  have hvemb : Topology.IsEmbedding (fun z : T => v z) :=
    Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  have hvlevel (t : ℝ) : v '' (N.space ×ˢ {t}) = c '' (N.space ×ˢ {a * t}) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨A z, ⟨hz.1, by change a * z.2 = a * t; rw [hz.2]⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.1, t), ⟨hz.1, rfl⟩, ?_⟩
      change c (z.1, a * t) = c z
      rw [← hz.2]
  have hvend : v '' (N.space ×ˢ {eps}) =
      c '' (N.space ×ˢ {if side then eps else -eps}) := by
    rw [hvlevel]
    cases side <;> simp [a]
  have hvzero : v '' (N.space ×ˢ {(0 : ℝ)}) = S := by
    rw [hvlevel, mul_zero]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have ht : z.2 = 0 := hz.2
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hcenter ⟨z.1, hz.1⟩]
      exact (HB ⟨z.1, hz.1⟩).property
    · intro hx
      refine ⟨(((HB.symm ⟨x, hx⟩ : N.space) : E), 0),
        ⟨(HB.symm ⟨x, hx⟩).property, rfl⟩, ?_⟩
      rw [hcenter]
      exact congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩)
  have hhalf : v '' (N.space ×ˢ Icc 0 eps) =
      c '' (N.space ×ˢ (if side then Icc 0 eps else Icc (-eps) 0)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨A z, ⟨hz.1, ?_⟩, rfl⟩
      change a * z.2 ∈ (if side then Icc 0 eps else Icc (-eps) 0)
      cases side <;> simp only [a, Bool.false_eq_true, ↓reduceIte, neg_mul,
        one_mul, mem_Icc] <;> constructor <;> linarith [hz.2.1, hz.2.2]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(z.1, a * z.2), ⟨hz.1, ?_⟩, ?_⟩
      · cases side <;> simp_all only [a, Bool.false_eq_true, ↓reduceIte,
          neg_mul, one_mul, mem_Icc] <;> constructor <;> linarith [hz.2.1, hz.2.2]
      · change c (z.1, a * (a * z.2)) = c z
        cases side <;> simp [a]
  have hoverlap : D ∩ v '' (N.space ×ˢ Icc 0 eps) =
      v '' (N.space ×ˢ {eps}) := by
    apply Subset.antisymm
    · rintro x ⟨hxD, z, hz, rfl⟩
      have ht : z.2 = eps := le_antisymm hz.2.2 (le_of_not_gt (by
        intro hlt
        apply (hD hxD).2
        refine ⟨A z, ⟨hz.1, ?_⟩, rfl⟩
        change -eps < a * z.2 ∧ a * z.2 < eps
        cases side <;> simp only [a, Bool.false_eq_true, ↓reduceIte,
          neg_mul, one_mul] <;> constructor <;> linarith [hz.2.1]))
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · intro x hx
      refine ⟨ball.boundary_subset (hvend.subset hx), ?_⟩
      apply image_mono (prod_mono Subset.rfl ?_) hx
      exact singleton_subset_iff.mpr ⟨heps.le, le_rfl⟩
  have bv : ChartwisePLBall e D (v '' (N.space ×ˢ {eps})) := hvend.symm ▸ ball
  obtain ⟨hball, hinterior⟩ := bv.attach_outer_strip hcover hcompat N hN v hv hvemb
    heps heps1 hoverlap
  rw [hhalf, hvzero] at hball
  rw [hhalf] at hinterior
  refine ⟨hball, hinterior, union_subset (fun x hx => (hD hx).1) ?_⟩
  apply Subset.trans (image_mono (prod_mono Subset.rfl ?_)) hstrip
  intro t ht
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_Icc] at ht ⊢ <;>
    constructor <;> linarith [ht.1, ht.2]

end PoincareConjecture.M76
