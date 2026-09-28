import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SeparatedSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SelectedCircleSurgeryFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCrossings










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_selected_circle_surgery_graph
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hG : G.faces.Finite) (hGQ : G.space ⊆ Q.target) {T : Set X}
    (hphysical : Q.symm '' G.space = (⋃ j, circleSurgeryFamily S i new j) ∩ T) :
    ∃ (H : SimplicialComplex ℝ V3) (hHG : H ≤ G), H.faces.Finite ∧
      H.space = G.space ∩ Q.symm ⁻¹' (⋃ j, selectedCircleSurgeryFamily S i new b j) ∧
      Q.symm '' H.space = (⋃ j, selectedCircleSurgeryFamily S i new b j) ∩ T ∧
      H.faces.ncard ≤ G.faces.ncard ∧
      ∀ v : H.vertices,
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
          (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val, hHG v.property⟩).ncard := by
  have hclosed : IsClosed (⋃ j, selectedCircleSurgeryFamily S i new b j) := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [selectedCircleSurgeryFamily_eq_index]
    exact (sfull _).isCompact.isClosed
  have homitted : IsClosed (new (!b)) := (sfull (Sum.inr (!b))).isCompact.isClosed
  have hcover : Q.symm '' G.space ⊆
      (⋃ j, selectedCircleSurgeryFamily S i new b j) ∪ new (!b) := by
    rw [selectedCircleSurgeryFamily_union_omitted, hphysical]
    exact inter_subset_left
  obtain ⟨H, hHG, hH, hspace, himage, hdegree⟩ :=
    G.exists_subcomplex_of_closed_image_partition hG Q.symm
      (Q.continuousOn_symm.mono hGQ) hclosed homitted
      (selectedCircleSurgeryFamily_disjoint_omitted S i new b hfull) hcover
  refine ⟨H, hHG, hH, hspace, ?_, Set.ncard_le_ncard hHG hG, hdegree⟩
  rw [himage, hphysical]
  ext x
  constructor
  · exact fun hx => ⟨hx.2, hx.1.2⟩
  · exact fun hx => ⟨⟨selectedCircleSurgeryFamily_subset S i new b hx.1, hx.2⟩, hx.1⟩

theorem selected_circle_surgery_paired_crossings
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    (Q : OpenPartialHomeomorph X V3) {w : V3} {T : Set V3}
    (hwQ : w ∈ Q.target)
    (hw : Q.symm w ∈ ⋃ j, selectedCircleSurgeryFamily S i new b j)
    (hcrossing : ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ ⋃ j, circleSurgeryFamily S i new j ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0) :
    ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ ⋃ j, selectedCircleSurgeryFamily S i new b j ↔
          (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T ↔ (B x).1.1 = 0 := by
  have hdis := selectedCircleSurgeryFamily_disjoint_omitted S i new b hfull
  have houtside : (⋃ j, selectedCircleSurgeryFamily S i new b j) \ new (!b) =
      (⋃ j, circleSurgeryFamily S i new j) \ new (!b) := by
    rw [← selectedCircleSurgeryFamily_union_omitted S i new b, union_sdiff_right]
  exact paired_face_crossings_of_equal_off_closed Q
    (sfull (Sum.inr (!b))).isCompact.isClosed houtside hwQ
    (fun hx => disjoint_left.mp hdis hw hx) hcrossing

end PoincareConjecture.M76
