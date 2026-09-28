import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.TubeNormal
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInterior








set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def tubeNormalCoordinates (side : Bool) : C3 ≃L[ℝ] C3 where
  toFun z := ((z.1.1, z.2), tubeNormal side z)
  invFun z := ((z.1.1, if side then -(z.2 + z.1.1) else z.2 + z.1.1), z.1.2)
  left_inv := by
    rintro ⟨⟨x, y⟩, t⟩
    cases side <;> simp [tubeNormal]
  right_inv := by
    rintro ⟨⟨x, t⟩, n⟩
    cases side <;> simp [tubeNormal]
  map_add' := by
    intro x y
    cases side <;> ext <;> simp [tubeNormal] <;> ring
  map_smul' := by
    intro a x
    cases side <;> ext <;> simp [tubeNormal, mul_sub]
  continuous_toFun := by
    cases side <;> simp only [tubeNormal, Bool.false_eq_true, if_false, if_true] <;> fun_prop
  continuous_invFun := by
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem exists_original_tube_normal_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool) :
    ∃ Q : OpenPartialHomeomorph X C3,
      Q.source = U.map '' interior tube ∧
      Q.target = tubeNormalCoordinates side '' interior tube ∧
      (∀ z ∈ interior tube, Q (U.map z) = ((z.1.1, z.2), tubeNormal side z)) ∧
      ∀ x ∈ Q.source, (Q x).2 = 0 ↔ x ∈ (if side then f₁ '' T else f₀ '' S) := by
  classical
  have hdim : Module.finrank ℝ C3 = Module.finrank ℝ V3 := by simp
  have himage : U.map '' interior tube = interior (U.map '' tube) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact (U.pl.mem_interior_image_iff hdim U.embedding ⟨z, interior_subset hz⟩).mpr hz
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := interior_subset hx
      exact ⟨z, (U.pl.mem_interior_image_iff hdim U.embedding ⟨z, hz⟩).mp hx, rfl⟩
  have hopen : IsOpen (U.map '' interior tube) := himage.symm ▸ isOpen_interior
  let f : interior tube → X := fun z => U.map z
  have hemb : IsEmbedding f := U.embedding.comp (IsEmbedding.inclusion interior_subset)
  have hrange : range f = U.map '' interior tube := by
    ext x
    simp only [f, mem_range, mem_image]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hpoint : ((0, 0), (1 / 2 : ℝ)) ∈ interior tube := by
    simp only [tube, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo]
    norm_num
  let : Nonempty (interior tube) := ⟨⟨_, hpoint⟩⟩
  have hopenEmbedding : IsOpenEmbedding f := ⟨hemb, hrange.symm ▸ hopen⟩
  let H := hopenEmbedding.toOpenPartialHomeomorph f
  let inclusion := (⟨interior tube, isOpen_interior⟩ : TopologicalSpace.Opens C3).openPartialHomeomorphSubtypeCoe inferInstance
  let B := H.symm.trans inclusion
  have hBs : B.source = U.map '' interior tube := by
    simp [B, H, inclusion, hrange]
  have hBt : B.target = interior tube := by
    simp [B, H, inclusion]
  have hBvalue (z : C3) (hz : z ∈ interior tube) : B (U.map z) = z := by
    change (H.symm (f ⟨z, hz⟩) : C3) = z
    rw [hopenEmbedding.toOpenPartialHomeomorph_left_inv]
  let Q := B.transHomeomorph (tubeNormalCoordinates side).toHomeomorph
  have hQs : Q.source = U.map '' interior tube := hBs
  have hQt : Q.target = tubeNormalCoordinates side '' interior tube := by
    change (tubeNormalCoordinates side).symm ⁻¹' B.target = _
    rw [hBt]
    ext z
    constructor
    · intro hz
      exact ⟨(tubeNormalCoordinates side).symm z, hz,
        (tubeNormalCoordinates side).apply_symm_apply z⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  have hvalue (z : C3) (hz : z ∈ interior tube) :
      Q (U.map z) = ((z.1.1, z.2), tubeNormal side z) := by
    change tubeNormalCoordinates side (B (U.map z)) = _
    rw [hBvalue z hz]
    rfl
  refine ⟨Q, hQs, hQt, hvalue, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hQs ▸ hx
  rw [hvalue z hz]
  cases side
  · simp only [Bool.false_eq_true, if_false, tubeNormal]
    exact sub_eq_zero.trans (U.first_trace z (interior_subset hz)).symm
  · simp only [if_true, tubeNormal]
    rw [U.second_trace z (interior_subset hz)]
    constructor <;> intro h <;> linarith

theorem original_tube_interior_disjoint_frontier
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) :
    Disjoint (U.map '' interior tube) (frontier R) := by
  apply disjoint_left.mpr
  rintro x ⟨z, hz, rfl⟩ hx
  have ht : z.2 ∈ Ioo (0 : ℝ) 1 := by
    simp only [tube, interior_prod_eq, interior_Icc, mem_prod] at hz
    exact hz.2
  rcases (U.frontier_iff z (interior_subset hz)).mp hx with h | h
  · exact (ne_of_gt ht.1) h
  · exact (ne_of_lt ht.2) h

theorem exists_original_tube_normal_chart_off_frontier
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool) :
    ∃ Q : OpenPartialHomeomorph X C3,
      Q.source = U.map '' interior tube ∧
      Q.target = tubeNormalCoordinates side '' interior tube ∧
      (∀ z ∈ interior tube, Q (U.map z) = ((z.1.1, z.2), tubeNormal side z)) ∧
      Disjoint Q.source (frontier R) ∧
      ∀ x ∈ Q.source, (Q x).2 = 0 ↔
        x ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R := by
  obtain ⟨Q, hsource, htarget, hvalue, hpair⟩ := exists_original_tube_normal_chart U side
  have hdis : Disjoint Q.source (frontier R) :=
    hsource.symm ▸ original_tube_interior_disjoint_frontier U
  refine ⟨Q, hsource, htarget, hvalue, hdis, ?_⟩
  intro x hx
  have hnot : x ∉ frontier R := fun h => disjoint_left.mp hdis hx h
  simpa only [mem_sdiff, hnot, not_false_eq_true, and_true] using hpair x hx

end PoincareConjecture.M76.Dehn.Annuli.RimBands
