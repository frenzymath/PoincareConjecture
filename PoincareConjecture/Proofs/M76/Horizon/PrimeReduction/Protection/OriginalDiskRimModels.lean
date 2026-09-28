import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedDiskComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAnnulusRimCircles
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedRimCircleModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentParametrization




set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76

theorem exists_marked_radius_sphere_circle_homeomorph
    {κ : Type*} [Fintype κ] (hdim : Fintype.card κ = 2) :
    Nonempty (sphere (0 : κ → ℝ) (3 / 2) ≃ₜ Circle) := by
  let T : (κ → ℝ) ≃ₜ (κ → ℝ) := Homeomorph.smulOfNeZero (2 / 3 : ℝ) (by norm_num)
  let h : sphere (0 : κ → ℝ) (3 / 2) ≃ₜ sphere (0 : κ → ℝ) 1 :=
    T.subtype (fun x => by
      change x ∈ sphere 0 (3 / 2) ↔ (2 / 3 : ℝ) • x ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, norm_smul]
      norm_num
      constructor <;> intro hx <;> linarith)
  obtain ⟨g⟩ := exists_unit_sphere_circle_homeomorph hdim
  exact ⟨h.trans g⟩

theorem exists_marked_disk_rim_circles
    {ι κ E : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    [TopologicalSpace E] [T2Space E] {T : Set E}
    (hdim : Fintype.card κ = 2)
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ T) :
    ∃ (S : Bool → Set E) (_H : ∀ side, S side ≃ₜ Circle),
      (∀ side, S side = range (fun x : sphere (0 : κ → ℝ) (3 / 2) =>
        (P ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
          (markedDiskSignCoordinates (ι := ι) side).property,
          sphere_subset_closedBall x.property⟩ : E))) ∧
      Pairwise (fun b c => Disjoint (S b) (S c)) ∧
      (⋃ side, S side) = (Subtype.val : T → E) ''
        (P '' {x | (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2)}) := by
  classical
  let f (side : Bool) (x : sphere (0 : κ → ℝ) (3 / 2)) : E :=
    P ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
      (markedDiskSignCoordinates (ι := ι) side).property,
      sphere_subset_closedBall x.property⟩
  have hf (side) : Continuous (f side) := continuous_subtype_val.comp
    (P.continuous.comp ((continuous_const.prodMk continuous_subtype_val).subtype_mk _))
  have hfi (side) : Function.Injective (f side) := by
    intro x y hxy
    exact Subtype.ext (congrArg Prod.snd
      (congrArg Subtype.val (P.injective (Subtype.ext hxy))))
  obtain ⟨g⟩ := exists_marked_radius_sphere_circle_homeomorph hdim
  let e (side) : sphere (0 : κ → ℝ) (3 / 2) ≃ₜ range (f side) :=
    (hf side).isClosedEmbedding (hfi side) |>.toHomeomorph
  refine ⟨fun side => range (f side), fun side => (e side).symm.trans g,
    fun _ => rfl, ?_, ?_⟩
  · intro b c hbc
    apply disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have heq := congrArg Prod.fst
      (congrArg Subtype.val (P.injective (Subtype.ext (hx.trans hy.symm))))
    exact hbc (markedDiskSignCoordinates.injective (Subtype.ext heq))
  · ext z
    constructor
    · intro hz
      obtain ⟨side, x, rfl⟩ := mem_iUnion.mp hz
      exact ⟨_, ⟨⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
        (markedDiskSignCoordinates (ι := ι) side).property, sphere_subset_closedBall x.property⟩,
        x.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨side, hside⟩ := (markedDiskSignCoordinates (ι := ι)).surjective
        ⟨x.val.1, x.property.1⟩
      apply mem_iUnion.mpr
      refine ⟨side, ⟨⟨x.val.2, hx⟩, ?_⟩⟩
      apply congrArg (fun z => (P z : E))
      exact Subtype.ext (Prod.ext (congrArg Subtype.val hside) rfl)

local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_original_disk_rim_models
    {ι κ α E : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hdim : Fintype.card κ = 2)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hfi : InjOn F (latticeHandleDomain ι κ L))
    (J B : SimplicialComplex ℝ E) (hB : B.faces.Finite)
    (hBdim : ∀ t ∈ B.faces, t.card ≤ 2)
    (hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2))
    (hBmark : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))) :
    ∃ (C : Bool → SimplicialComplex ℝ E)
      (gamma : ∀ side, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (C side).space),
      (∀ side, C side ≤ B ∧ (C side).faces.Finite ∧ (gamma side).IsFinitePL ∧
        (C side).space = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            sphere (0 : κ → ℝ) (3 / 2)))) ∧
      (∀ t, t ∈ B.faces ↔ ∃ side, t ∈ (C side).faces) := by
  classical
  obtain ⟨P, hP⟩ := b.exists_marked_image_homeomorph (by simp) F hF hfi
    (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)) subset_rfl J.space hJmark
  obtain ⟨S, H, hS, hdis, hcover⟩ := exists_marked_disk_rim_circles hdim P
  have hfull : (Subtype.val : J.space → E) ''
      (P '' {x | (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2)}) = B.space := by
    rw [hBmark]
    apply Subset.antisymm
    · rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, ⟨x.property.1, hx⟩, rfl⟩, (hP x).symm⟩
    · rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      let z : sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) :=
        ⟨x, hx.1, sphere_subset_closedBall hx.2⟩
      exact ⟨P z, ⟨z, hx.2, rfl⟩, hP z⟩
  obtain ⟨C, gamma, hC, hfaces⟩ := B.exists_marked_finitePL_circle_models
    hB hBdim S H hdis (hcover.trans hfull)
  refine ⟨C, gamma, ?_, hfaces⟩
  intro side
  refine ⟨(hC side).1, (hC side).2.1, (hC side).2.2.2, ?_⟩
  rw [(hC side).2.2.1, hS side]
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨_, ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
      ⟨?_, x.property⟩, rfl⟩, ?_⟩
    · exact markedDiskSignCoordinates_apply (ι := ι) side
    · exact (hP ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
        (markedDiskSignCoordinates (ι := ι) side).property,
        sphere_subset_closedBall x.property⟩).symm
  · rintro y ⟨_, ⟨x, ⟨hside, hx⟩, rfl⟩, rfl⟩
    refine ⟨⟨x.2, hx⟩, ?_⟩
    change (P ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), x.2),
      (markedDiskSignCoordinates (ι := ι) side).property, sphere_subset_closedBall hx⟩ : E) = _
    rw [hP]
    apply congrArg (F ∘ hamiltonMarkedProjection ι κ L)
    exact Prod.ext ((markedDiskSignCoordinates_apply (ι := ι) side).trans hside.symm) rfl

end PoincareConjecture.M76
