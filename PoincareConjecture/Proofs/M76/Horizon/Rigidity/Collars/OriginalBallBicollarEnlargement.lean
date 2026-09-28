import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallOuterAttachment
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLBall.exists_bicollar_enlargement
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) (sph : ChartwisePLSphere e S)
    (hcover_e : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ S) (c : E × ℝ → X)
    {r : ℝ} (hr : 0 < r)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hopen : IsOpen (c '' (L.space ×ˢ Ioo (-r) r))) :
    ∃ a : ℝ, (a = r ∨ a = -r) ∧ a ≠ 0 ∧ ∃ D' : Set X,
      Nonempty (ChartwisePLBall e D' (c '' (L.space ×ˢ {a}))) ∧
      D ⊆ interior D' ∧ D' ⊆ D ∪ c '' (L.space ×ˢ Icc (-r) r) := by
  obtain ⟨a, ha, hane, hmap, hout⟩ :
      ∃ a : ℝ, (a = r ∨ a = -r) ∧ a ≠ 0 ∧
        (∀ t ∈ I, a * (1 - t) ∈ Icc (-r) r) ∧
        (∀ z ∈ L.space, ∀ t ∈ Ico (0 : ℝ) 1, c (z, a * (1 - t)) ∉ D) := by
    rcases b.bicollar_sides sph L.space HB c hr hc.continuousOn hi hbase hopen
      with ⟨_, hneg⟩ | ⟨_, hpos⟩
    · refine ⟨-r, Or.inr rfl, neg_ne_zero.mpr hr.ne', ?_, ?_⟩
      · intro t ht
        constructor <;> nlinarith [ht.1, ht.2]
      · intro z hz t ht hD
        apply disjoint_left.mp hneg _ hD
        refine ⟨(z, -r * (1 - t)), ⟨hz, ?_, ?_⟩, rfl⟩ <;>
          nlinarith [ht.1, ht.2]
    · refine ⟨r, Or.inl rfl, hr.ne', ?_, ?_⟩
      · intro t ht
        constructor <;> nlinarith [ht.1, ht.2]
      · intro z hz t ht hD
        apply disjoint_left.mp hpos _ hD
        refine ⟨(z, r * (1 - t)), ⟨hz, ?_, ?_⟩, rfl⟩ <;>
          nlinarith [ht.1, ht.2]
  let A : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (a • (ContinuousAffineMap.const ℝ (E × ℝ) 1 -
        (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap))
  have hAval (z : E × ℝ) : A z = (z.1, a * (1 - z.2)) := rfl
  let v : E × ℝ → X := c ∘ A
  obtain ⟨K, hK, hKI⟩ := L.exists_finite_interval_product hL (by norm_num : (0 : ℝ) < 1)
  have hAmap : MapsTo A (L.space ×ˢ I) (L.space ×ˢ Icc (-r) r) := by
    intro z hz
    exact ⟨hz.1, hmap z.2 hz.2⟩
  have hv : PolyhedralPLInCharts e v (L.space ×ˢ I) := by
    have h := hc.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine A).finitePiecewiseAffineOn hK)
      (fun z hz => hAmap (hKI.subset hz))
    exact hKI ▸ h
  have hvinj : InjOn v (L.space ×ˢ I) := by
    intro z hz w hw heq
    have hAw : A z = A w := congrArg Subtype.val
      (hi.injective (a₁ := ⟨A z, hAmap hz⟩) (a₂ := ⟨A w, hAmap hw⟩) heq)
    have hfst := congrArg Prod.fst hAw
    have hsnd := congrArg Prod.snd hAw
    change a * (1 - z.2) = a * (1 - w.2) at hsnd
    have ht := mul_left_cancel₀ hane hsnd
    exact Prod.ext hfst (by linarith)
  let B : Set (E × ℝ) := L.space ×ˢ I
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    ((L.isCompact_space_of_finite hL).prod isCompact_Icc)
  let H : B ≃ₜ v '' B := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn v B hvinj) (hv.continuousOn.domRestrict.subtype_mk _)
  have hvemb : Topology.IsEmbedding (fun z : B => v z) :=
    Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  have hvone : v '' (L.space ×ˢ {(1 : ℝ)}) = S := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z.2 = 1 := hz.2
      change c (z.1, a * (1 - z.2)) ∈ S
      rw [hzt, sub_self, mul_zero, hbase ⟨z.1, hz.1⟩]
      exact (HB ⟨z.1, hz.1⟩).property
    · intro hx
      let z := HB.symm ⟨x, hx⟩
      refine ⟨((z : E), 1), ⟨z.property, rfl⟩, ?_⟩
      change c ((z : E), a * (1 - 1)) = x
      rw [sub_self, mul_zero, hbase]
      exact congrArg Subtype.val (HB.apply_symm_apply ⟨x, hx⟩)
  have hvoverlap : D ∩ v '' (L.space ×ˢ I) = v '' (L.space ×ˢ {(1 : ℝ)}) := by
    apply Subset.antisymm
    · rintro x ⟨hxD, z, hz, rfl⟩
      have ht : z.2 = 1 := le_antisymm hz.2.2 (le_of_not_gt (fun ht =>
        hout z.1 hz.1 z.2 ⟨hz.2.1, ht⟩ hxD))
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · intro x hx
      refine ⟨b.boundary_subset (hvone.subset hx), ?_⟩
      exact image_mono (prod_mono Subset.rfl (singleton_subset_iff.mpr (by norm_num))) hx
  have bv : ChartwisePLBall e D (v '' (L.space ×ˢ {(1 : ℝ)})) := hvone.symm ▸ b
  obtain ⟨hbnew, hDnew⟩ := bv.attach_outer_strip hcover_e hcompat L hL v hv hvemb
    (by norm_num : (0 : ℝ) < 1) le_rfl hvoverlap
  have hvzero : v '' (L.space ×ˢ {(0 : ℝ)}) = c '' (L.space ×ˢ {a}) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z.2 = 0 := hz.2
      refine ⟨(z.1, a), ⟨hz.1, rfl⟩, ?_⟩
      change c (z.1, a) = c (z.1, a * (1 - z.2))
      rw [hzt, sub_zero, mul_one]
    · rintro ⟨z, hz, rfl⟩
      have hzt : z.2 = a := hz.2
      refine ⟨(z.1, 0), ⟨hz.1, rfl⟩, ?_⟩
      change c (z.1, a * (1 - 0)) = c z
      rw [sub_zero, mul_one, ← hzt]
  refine ⟨a, ha, hane, D ∪ v '' B, hvzero ▸ hbnew, hDnew, ?_⟩
  apply union_subset_union_right
  rintro x ⟨z, hz, rfl⟩
  exact ⟨A z, hAmap hz, rfl⟩

end PoincareConjecture.M76
