import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Annulus

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

structure AnnulusSquareCopies {X : Type*} (f : Fin 2 → P2 → X) (g : P2 → X) where
  piece : Fin 2 → Set P2
  chart : ∀ j, Sq ≃ₜ piece j
  finitePL : ∀ j, (chart j).IsFinitePL
  cover : piece 0 ∪ piece 1 = squareAnnulus 8 1
  val : ∀ j (z : Sq), g (chart j z) = f j z
  cross : ∀ u v : Sq, (chart 0 u : P2) = chart 1 v ↔
    u = v ∧ ((u : P2).1 = 0 ∨ (u : P2).1 = 1)
  outer : ∀ j (z : Sq), depth 8 (chart j z : P2) = -1 ↔ (z : P2).2 = 0
  inner : ∀ j (z : Sq), depth 8 (chart j z : P2) = 1 ↔ (z : P2).2 = 1

namespace AnnulusSquareCopies

variable {X : Type*} {f : Fin 2 → P2 → X} {g : P2 → X} (C : AnnulusSquareCopies f g)

theorem chart_mem (j : Fin 2) (z : Sq) : (C.chart j z : P2) ∈ squareAnnulus 8 1 := by
  apply C.cover.subset
  fin_cases j
  · exact Or.inl (C.chart 0 z).property
  · exact Or.inr (C.chart 1 z).property

theorem exists_representation {x : P2} (hx : x ∈ squareAnnulus 8 1) :
    ∃ (j : Fin 2) (z : Sq), (C.chart j z : P2) = x := by
  rcases C.cover.symm.subset hx with hx | hx
  · exact ⟨0, (C.chart 0).symm ⟨x, hx⟩,
      congrArg Subtype.val ((C.chart 0).apply_symm_apply ⟨x, hx⟩)⟩
  · exact ⟨1, (C.chart 1).symm ⟨x, hx⟩,
      congrArg Subtype.val ((C.chart 1).apply_symm_apply ⟨x, hx⟩)⟩

theorem preimage (U : Set X) : squareAnnulus 8 1 ∩ g ⁻¹' U =
    ((fun z : Sq ↦ (C.chart 0 z : P2)) '' {z | f 0 z ∈ U}) ∪
      ((fun z : Sq ↦ (C.chart 1 z : P2)) '' {z | f 1 z ∈ U}) := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxU⟩
    obtain ⟨j, z, rfl⟩ := C.exists_representation hx
    change g (C.chart j z) ∈ U at hxU
    rw [C.val] at hxU
    fin_cases j
    · exact Or.inl ⟨z, hxU, rfl⟩
    · exact Or.inr ⟨z, hxU, rfl⟩
  · rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨C.chart_mem 0 z, by simpa only [mem_preimage, C.val, mem_ofPred_eq] using hz⟩
    · exact ⟨C.chart_mem 1 z, by simpa only [mem_preimage, C.val, mem_ofPred_eq] using hz⟩

include C in
theorem injective_iff : InjOn g (squareAnnulus 8 1) ↔
    (∀ j, InjOn (f j) Sq) ∧
      (∀ u v : Sq, f 0 u = f 1 v → u = v ∧ ((u : P2).1 = 0 ∨ (u : P2).1 = 1)) := by
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · intro j u hu v hv huv
      have he := hg (C.chart_mem j ⟨u, hu⟩) (C.chart_mem j ⟨v, hv⟩)
        (by simpa only [C.val] using huv)
      exact congrArg Subtype.val ((C.chart j).injective (Subtype.ext he))
    · intro u v huv
      exact (C.cross u v).mp (hg (C.chart_mem 0 u) (C.chart_mem 1 v)
        (by simpa only [C.val] using huv))
  · rintro ⟨hf, hcross⟩ x hx y hy hxy
    obtain ⟨j, u, rfl⟩ := C.exists_representation hx
    obtain ⟨k, v, rfl⟩ := C.exists_representation hy
    rw [C.val, C.val] at hxy
    fin_cases j <;> fin_cases k
    · exact congrArg (fun z : Sq ↦ (C.chart 0 z : P2))
        (Subtype.ext (hf 0 u.property v.property hxy))
    · exact (C.cross u v).mpr (hcross u v hxy)
    · exact ((C.cross v u).mpr (hcross v u hxy.symm)).symm
    · exact congrArg (fun z : Sq ↦ (C.chart 1 z : P2))
        (Subtype.ext (hf 1 u.property v.property hxy))

end AnnulusSquareCopies

theorem exists_standard_annulus_map_with_copies
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (f : Fin 2 → P2 → X) (hf : ∀ j, PolyhedralPLInCharts e (f j) Sq)
    (hleft : ∀ t : I, f 0 (0, t) = f 1 (0, t))
    (hright : ∀ t : I, f 0 (1, t) = f 1 (1, t)) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g (squareAnnulus 8 1) ∧
      Nonempty (AnnulusSquareCopies f g) := by
  let S : Set P2 := Dehn.annulusSquare 8 1
  let T : Set P2 := Dehn.annulusSquare 8 (-1)
  have hS : IsFinitePLBallPair P2 S (frontier S) := Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hT : IsFinitePLBallPair P2 T (frontier T) := Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hST : S ⊆ interior T := by
    intro z hz
    have hh := (Dehn.mem_annulusSquare_iff 8 1 z).mp hz
    apply (Dehn.mem_interior_annulusSquare_iff 8 (-1) z).mpr
    linarith
  have hAnn : T \ interior S = squareAnnulus 8 1 := by
    ext z
    rw [mem_sdiff, Dehn.mem_annulusSquare_iff, Dehn.mem_interior_annulusSquare_iff,
      mem_squareAnnulus_iff_depth, mem_Icc]
    exact and_congr_right (fun _ ↦ not_lt)
  obtain ⟨D⟩ := exists_nested_shell_dissection hS hT hST
  obtain ⟨C⟩ := D.nonempty_square_charts
  obtain ⟨g, hg, hval, _⟩ := C.exists_target_map_union hcompat f hf hleft hright
  refine ⟨g, hAnn ▸ hg, ⟨⟨D.disk, C.chart, C.finitePL, D.disk_cover.trans hAnn,
    hval, ?_, ?_, ?_⟩⟩⟩
  · intro u v
    constructor
    · intro huv
      have hside := (C.mem_other_disk_iff u).mp (huv ▸ (C.chart 1 v).property)
      have he : u = v := (C.chart 1).injective (Subtype.ext ((C.agree_at_side u hside).symm.trans huv))
      exact ⟨he, hside⟩
    · rintro ⟨rfl, hside⟩
      exact C.agree_at_side u hside
  · intro j z
    exact (Dehn.mem_frontier_annulusSquare_iff 8 (-1) (C.chart j z)).symm.trans
      ((D.outer_in_disk_iff j (C.chart j z)).trans (C.outer_iff j z))
  · intro j z
    exact (Dehn.mem_frontier_annulusSquare_iff 8 1 (C.chart j z)).symm.trans
      ((D.inner_in_disk_iff j (C.chart j z)).trans (C.inner_iff j z))

end PoincareConjecture.M76.Dehn
