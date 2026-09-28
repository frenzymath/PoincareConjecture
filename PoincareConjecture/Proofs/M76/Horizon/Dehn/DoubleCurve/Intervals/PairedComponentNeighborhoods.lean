import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.PairedSourceNeighborhoods
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.OrdinaryArcParameters









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}


theorem OrdinaryDoubleCurveModel.injOn_piece_of_mate_ne
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) (hi : M.mate i ≠ i) :
    InjOn f (M.pieces i) := by
  intro x hx y hy hxy
  by_contra hne
  have hxG := M.piece_subset_double i hx
  have hpartner := M.unique_partner ⟨x, hxG⟩ y
    (M.piece_subset_double i hy).1 hxy hne
  exact disjoint_left.mp (M.disjoint hi)
    (M.partner_component i ⟨x, hxG⟩ hx) (hpartner ▸ hy)


theorem OrdinaryDoubleCurveModel.piece_image_preimage
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) (x : V2) (hx : x ∈ D2) :
    f x ∈ f '' M.pieces i ↔ x ∈ M.pieces i ∪ M.pieces (M.mate i) := by
  constructor
  · rintro ⟨y, hy, hfy⟩
    by_cases hyx : y = x
    · exact Or.inl (hyx ▸ hy)
    · have h := M.unique_partner ⟨y, M.piece_subset_double i hy⟩ x hx hfy hyx
      exact Or.inr (h.symm ▸ M.partner_component i ⟨y, M.piece_subset_double i hy⟩ hy)
  · rintro (hi | hm)
    · exact ⟨x, hi, rfl⟩
    · let z : doubleLocusOn f D2 := ⟨x, M.piece_subset_double (M.mate i) hm⟩
      have hz := M.partner_component (M.mate i) z hm
      rw [M.mate_involutive i] at hz
      exact ⟨M.partner z, hz, M.partner_value z⟩


theorem OrdinaryDoubleCurveModel.piece_image_mate
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) :
    f '' M.pieces (M.mate i) = f '' M.pieces i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (M.piece_image_preimage i x (M.piece_subset_double (M.mate i) hx).1).mpr
      (Or.inr hx)
  · rintro ⟨x, hx, rfl⟩
    apply (M.piece_image_preimage (M.mate i) x (M.piece_subset_double i hx).1).mpr
    right
    simpa only [M.mate_involutive i] using hx



theorem OrdinaryDoubleCurveModel.exists_paired_component_neighborhoods
    [T2Space X] (M : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (i : M.Index) (hi : M.mate i ≠ i) :
    ∃ (P Q : SimplicialComplex ℝ V2) (U V : Set D2) (O : Set X),
      P.faces.Finite ∧ Q.faces.Finite ∧ P.space ⊆ D2 ∧ Q.space ⊆ D2 ∧
      Disjoint P.space Q.space ∧ IsOpen U ∧ IsOpen V ∧
      (Subtype.val : D2 → V2) ⁻¹' M.pieces i ⊆ U ∧
      (Subtype.val : D2 → V2) ⁻¹' M.pieces (M.mate i) ⊆ V ∧
      Subtype.val '' U ⊆ P.space ∧ Subtype.val '' V ⊆ Q.space ∧
      M.pieces i ⊆ P.space ∧ M.pieces (M.mate i) ⊆ Q.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ IsEmbedding (fun x : Q.space ↦ f x) ∧
      PolyhedralPLInCharts e f P.space ∧ PolyhedralPLInCharts e f Q.space ∧
      IsOpen O ∧ f '' M.pieces i ⊆ O ∧
      (∀ x ∈ D2, f x ∈ O → x ∈ P.space ∪ Q.space) ∧
      O ∩ (f '' P.space ∩ f '' Q.space) = f '' M.pieces i := by
  classical
  have : Finite M.Index := M.finiteIndex
  have him : M.mate (M.mate i) ≠ M.mate i := by
    rw [M.mate_involutive i]
    exact hi.symm
  obtain ⟨P, Q, U, V, O₀, hP, hQ, hPD, hQD, hPQ, hU, hV,
      hiU, hmV, hUP, hVQ, hPi, hQi, hPPL, hQPL, hO₀, hTO₀, hfull⟩ :=
    M.exists_paired_source_neighborhoods hf (M.compact i) (M.compact (M.mate i))
      (M.piece_subset_double i) (M.piece_subset_double (M.mate i))
      (M.disjoint hi.symm) (M.injOn_piece_of_mate_ne i hi)
      (M.injOn_piece_of_mate_ne (M.mate i) him) (M.piece_image_preimage i)
  have hiP : M.pieces i ⊆ P.space := by
    intro x hx
    exact hUP ⟨⟨x, (M.piece_subset_double i hx).1⟩, hiU hx, rfl⟩
  have hmQ : M.pieces (M.mate i) ⊆ Q.space := by
    intro x hx
    exact hVQ ⟨⟨x, (M.piece_subset_double (M.mate i) hx).1⟩, hmV hx, rfl⟩
  let C : Set V2 := ⋃ j : {j : M.Index // j ≠ i ∧ j ≠ M.mate i}, M.pieces j.val
  have hCc : IsCompact C := isCompact_iUnion (fun j ↦ M.compact j.val)
  have hCD : C ⊆ D2 := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (M.piece_subset_double j.val hj).1
  have himageC : IsClosed (f '' C) :=
    (hCc.image_of_continuousOn (hf.continuousOn.mono hCD)).isClosed
  let O := O₀ \ (f '' C)
  have hTO : f '' M.pieces i ⊆ O := by
    intro y hy
    refine ⟨hTO₀ hy, ?_⟩
    rintro ⟨x, hx, hxy⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hxT : f x ∈ f '' M.pieces i := hxy.symm ▸ hy
    rcases (M.piece_image_preimage i x (M.piece_subset_double j.val hj).1).mp hxT with ha | hb
    · exact disjoint_left.mp (M.disjoint j.property.1) hj ha
    · exact disjoint_left.mp (M.disjoint j.property.2) hj hb
  refine ⟨P, Q, U, V, O, hP, hQ, hPD, hQD, hPQ, hU, hV, hiU, hmV, hUP, hVQ,
    hiP, hmQ, hPi, hQi, hPPL, hQPL, hO₀.sdiff himageC, hTO,
    fun x hx hfx ↦ hfull x hx hfx.1, ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨hyO, ⟨x, hxP, hxy⟩, z, hzQ, hzy⟩
    have hxz : x ≠ z := by
      rintro rfl
      exact disjoint_left.mp hPQ hxP hzQ
    have hxG : x ∈ doubleLocusOn f D2 := ⟨hPD hxP, z, hQD hzQ, hxy.trans hzy.symm, hxz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (M.cover.symm ▸ hxG)
    by_cases hji : j = i
    · exact ⟨x, hji ▸ hj, hxy⟩
    by_cases hjm : j = M.mate i
    · rw [← M.piece_image_mate i]
      exact ⟨x, hjm ▸ hj, hxy⟩
    · exact (hyO.2 ⟨x, mem_iUnion.mpr ⟨⟨j, hji, hjm⟩, hj⟩, hxy⟩).elim
  · intro y hy
    refine ⟨hTO hy, image_mono hiP hy, ?_⟩
    exact image_mono hmQ (M.piece_image_mate i ▸ hy)

end PoincareConjecture.M76.Dehn
