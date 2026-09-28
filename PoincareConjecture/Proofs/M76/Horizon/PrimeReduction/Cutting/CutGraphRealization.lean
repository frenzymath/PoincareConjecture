import PoincareConjecture.Proofs.M76.Mathlib.BarycentricRealization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions

set_option autoImplicit false

open Set Geometry StdSimplexCore

namespace PoincareConjecture.M76.CutGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

abbrev Coordinate (V I : Type*) := V ⊕ (I × Bool)
abbrev Ambient (V I : Type*) := Coordinate V I → ℝ

noncomputable def vertex (v : V) : Ambient V I := Pi.single (Sum.inl v) 1
noncomputable def privateVertex (i : I) (b : Bool) : Ambient V I :=
  Pi.single (Sum.inr (i, b)) 1

def arm (ends : I → Bool → V) (i : I) (b : Bool) : Set (Ambient V I) :=
  barycentricFace {Sum.inl (ends i b), Sum.inr (i, b)}

def bridge (i : I) : Set (Ambient V I) :=
  barycentricFace {Sum.inr (i, false), Sum.inr (i, true)}

def edge (ends : I → Bool → V) (i : I) : Set (Ambient V I) :=
  arm ends i false ∪ bridge i ∪ arm ends i true

def carrier (ends : I → Bool → V) : Set (Ambient V I) :=
  Set.range vertex ∪ ⋃ i, edge ends i

private theorem face_inter {J : Type*} [Fintype J] [DecidableEq J]
    (s t : Finset J) :
    barycentricFace s ∩ barycentricFace t = barycentricFace (s ∩ t) := by
  ext x
  simp only [barycentricFace, mem_inter_iff, mem_ofPred_eq, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hx, hs⟩, _, ht⟩
    refine ⟨hx, fun j hj => ?_⟩
    by_cases hjs : j ∈ s
    · exact ht j (fun hjt => hj ⟨hjs, hjt⟩)
    · exact hs j hjs
  · rintro ⟨hx, h⟩
    exact ⟨⟨hx, fun j hj => h j (fun hh => hj hh.1)⟩,
      hx, fun j hj => h j (fun hh => hj hh.2)⟩

private theorem face_pair {J : Type*} [Fintype J] [DecidableEq J] (a b : J) :
    barycentricFace {a, b} = segment ℝ (Pi.single a 1) (Pi.single b 1) := by
  rw [barycentricFace_eq_convexHull]
  simp only [Finset.coe_pair, image_pair, convexHull_pair]

private theorem face_singleton {J : Type*} [Fintype J] [DecidableEq J] (a : J) :
    barycentricFace {a} = {Pi.single a (1 : ℝ)} := by
  rw [barycentricFace_eq_convexHull]
  simp

private theorem face_empty {J : Type*} [Fintype J] [DecidableEq J] :
    barycentricFace (∅ : Finset J) = ∅ := by
  rw [barycentricFace_eq_convexHull]
  simp

theorem arm_eq_segment (ends : I → Bool → V) (i : I) (b : Bool) :
    arm ends i b = segment ℝ (vertex (ends i b)) (privateVertex i b) :=
  face_pair _ _

theorem bridge_eq_segment (i : I) :
    (bridge i : Set (Ambient V I)) =
      segment ℝ (privateVertex i false) (privateVertex i true) := face_pair _ _

theorem endpoint_mem_edge (ends : I → Bool → V) (i : I) (b : Bool) :
    vertex (ends i b) ∈ edge ends i := by
  cases b
  · exact Or.inl (Or.inl ((arm_eq_segment ends i false).symm ▸ left_mem_segment _ _ _))
  · exact Or.inr ((arm_eq_segment ends i true).symm ▸ left_mem_segment _ _ _)

theorem arm_inter_arm (ends : I → Bool → V) {i j : I} (hij : i ≠ j)
    (a b : Bool) :
    arm ends i a ∩ arm ends j b =
      if ends i a = ends j b then {vertex (ends i a)} else ∅ := by
  rw [arm, arm, face_inter]
  by_cases h : ends i a = ends j b
  · simp [h, hij, face_singleton, vertex]
  · simp [h, hij, face_empty]

theorem bridge_inter_arm (ends : I → Bool → V) {i j : I} (hij : i ≠ j)
    (b : Bool) : bridge i ∩ arm ends j b = ∅ := by
  rw [bridge, arm, face_inter]
  simp [hij, face_empty]

theorem bridge_inter_bridge {i j : I} (hij : i ≠ j) :
    (bridge i : Set (Ambient V I)) ∩ bridge j = ∅ := by
  rw [bridge, bridge, face_inter]
  simp [hij, face_empty]

theorem mem_edge_inter_iff (ends : I → Bool → V) {i j : I} (hij : i ≠ j)
    (x : Ambient V I) :
    x ∈ edge ends i ∩ edge ends j ↔
      ∃ a b, ends i a = ends j b ∧ x = vertex (ends i a) := by
  have haa (a b : Bool) : x ∈ arm ends i a ∩ arm ends j b ↔
      ends i a = ends j b ∧ x = vertex (ends i a) := by
    rw [arm_inter_arm ends hij]
    split_ifs <;> simp_all
  constructor
  · rintro ⟨(hi | hi) | hi, (hj | hj) | hj⟩
    · exact ⟨false, false, (haa false false).mp ⟨hi, hj⟩⟩
    · have := bridge_inter_arm ends (Ne.symm hij) false
      exact False.elim (by simpa [this] using (show x ∈ bridge j ∩ arm ends i false from ⟨hj, hi⟩))
    · exact ⟨false, true, (haa false true).mp ⟨hi, hj⟩⟩
    · have := bridge_inter_arm ends hij false
      exact False.elim (by simpa [this] using (show x ∈ bridge i ∩ arm ends j false from ⟨hi, hj⟩))
    · have := bridge_inter_bridge (V := V) hij
      exact False.elim (by simpa [this] using (show x ∈ bridge i ∩ bridge j from ⟨hi, hj⟩))
    · have := bridge_inter_arm ends hij true
      exact False.elim (by simpa [this] using (show x ∈ bridge i ∩ arm ends j true from ⟨hi, hj⟩))
    · exact ⟨true, false, (haa true false).mp ⟨hi, hj⟩⟩
    · have := bridge_inter_arm ends (Ne.symm hij) true
      exact False.elim (by simpa [this] using (show x ∈ bridge j ∩ arm ends i true from ⟨hj, hi⟩))
    · exact ⟨true, true, (haa true true).mp ⟨hi, hj⟩⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨endpoint_mem_edge ends i a, h ▸ endpoint_mem_edge ends j b⟩

theorem disjoint_edge_interiors (ends : I → Bool → V) {i j : I} (hij : i ≠ j) :
    Disjoint (edge ends i \ Set.range vertex) (edge ends j \ Set.range vertex) := by
  rw [Set.disjoint_left]
  rintro x ⟨hi, hvi⟩ ⟨hj, _⟩
  obtain ⟨a, _, _, rfl⟩ := (mem_edge_inter_iff ends hij x).mp ⟨hi, hj⟩
  exact hvi ⟨ends i a, rfl⟩

theorem vertex_mem_carrier (ends : I → Bool → V) (v : V) :
    vertex v ∈ carrier ends := Or.inl ⟨v, rfl⟩

theorem edge_subset_carrier (ends : I → Bool → V) (i : I) :
    edge ends i ⊆ carrier ends := fun _ hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩)

theorem privateVertex_mem_edge (ends : I → Bool → V) (i : I) (b : Bool) :
    privateVertex i b ∈ edge ends i := by
  cases b
  · exact Or.inl (Or.inl ((arm_eq_segment ends i false).symm ▸ right_mem_segment _ _ _))
  · exact Or.inr ((arm_eq_segment ends i true).symm ▸ right_mem_segment _ _ _)

noncomputable def edgePath (ends : I → Bool → V) (i : I) :
    Path (⟨vertex (ends i false), vertex_mem_carrier ends _⟩ : carrier ends)
      ⟨vertex (ends i true), vertex_mem_carrier ends _⟩ := by
  let u : carrier ends := ⟨privateVertex i false,
    edge_subset_carrier ends i (privateVertex_mem_edge ends i false)⟩
  let v : carrier ends := ⟨privateVertex i true,
    edge_subset_carrier ends i (privateVertex_mem_edge ends i true)⟩
  have h₀ : segment ℝ (vertex (ends i false)) (u : Ambient V I) ⊆ carrier ends := by
    rw [← arm_eq_segment]
    exact fun _ hx => edge_subset_carrier ends i (Or.inl (Or.inl hx))
  have h₁ : segment ℝ (u : Ambient V I) (v : Ambient V I) ⊆ carrier ends := by
    rw [← bridge_eq_segment]
    exact fun _ hx => edge_subset_carrier ends i (Or.inl (Or.inr hx))
  have h₂ : segment ℝ (v : Ambient V I) (vertex (ends i true)) ⊆ carrier ends := by
    rw [segment_symm, ← arm_eq_segment]
    exact fun _ hx => edge_subset_carrier ends i (Or.inr hx)
  exact ((Path.segmentIn _ _ u h₀).trans (Path.segmentIn _ u v h₁)).trans
    (Path.segmentIn _ v _ h₂)

theorem edgePath_zero (ends : I → Bool → V) (i : I) :
    (edgePath ends i 0 : Ambient V I) = vertex (ends i false) :=
  congrArg Subtype.val (edgePath ends i).source

theorem edgePath_one (ends : I → Bool → V) (i : I) :
    (edgePath ends i 1 : Ambient V I) = vertex (ends i true) :=
  congrArg Subtype.val (edgePath ends i).target

theorem continuous_edgePath (ends : I → Bool → V) (i : I) :
    Continuous (fun t => (edgePath ends i t : Ambient V I)) :=
  continuous_subtype_val.comp (edgePath ends i).continuous

private theorem image_range_segmentIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : Set E) (a b : s)
    (h : segment ℝ (a : E) (b : E) ⊆ s) :
    Subtype.val '' Set.range (Path.segmentIn s a b h) =
      segment ℝ (a : E) (b : E) := by
  rw [← Set.range_comp]
  exact Path.range_segment _ _

theorem range_edgePath (ends : I → Bool → V) (i : I) :
    Set.range (fun t => (edgePath ends i t : Ambient V I)) = edge ends i := by
  change Set.range (Subtype.val ∘ edgePath ends i) = _
  rw [Set.range_comp]
  unfold edgePath
  simp only [Path.trans_range, Set.image_union, image_range_segmentIn]
  rw [segment_symm ℝ (privateVertex i true) (vertex (ends i true))]
  rw [← arm_eq_segment, ← arm_eq_segment, ← bridge_eq_segment]
  rfl

theorem exists_finite_triangulation (ends : I → Bool → V) :
    ∃ K : SimplicialComplex ℝ (Ambient V I), K.faces.Finite ∧ K.space = carrier ends := by
  classical
  let labels : V ⊕ (I × Option Bool) → Finset (Coordinate V I)
    | .inl v => {Sum.inl v}
    | .inr (i, none) => {Sum.inr (i, false), Sum.inr (i, true)}
    | .inr (i, some b) => {Sum.inl (ends i b), Sum.inr (i, b)}
  let p : Coordinate V I → Ambient V I := fun j => Pi.single j 1
  let T := fun j => (labels j).image p
  have hT : ∀ j, AffineIndependent ℝ ((↑) : T j → Ambient V I) := by
    intro j
    apply (Pi.linearIndependent_single_one (Coordinate V I) ℝ).affineIndependent.range.mono
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem_range_self k
  obtain ⟨K, hK, hKs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull T hT
  refine ⟨K, hK, hKs.trans ?_⟩
  have he (j) : convexHull ℝ (T j : Set (Ambient V I)) = barycentricFace (labels j) := by
    rw [barycentricFace_eq_convexHull]
    simp only [T, Finset.coe_image]
    rfl
  simp_rw [he]
  ext x
  simp only [mem_iUnion, Sum.exists, Prod.exists, Option.exists, labels, face_singleton,
    mem_singleton_iff, carrier, mem_union, mem_range, edge, arm, bridge]
  constructor
  · rintro (⟨v, hv⟩ | ⟨i, hi | ⟨b, hb⟩⟩)
    · exact Or.inl ⟨v, hv.symm⟩
    · exact Or.inr ⟨i, Or.inl (Or.inr hi)⟩
    · cases b
      · exact Or.inr ⟨i, Or.inl (Or.inl hb)⟩
      · exact Or.inr ⟨i, Or.inr hb⟩
  · rintro (⟨v, hv⟩ | ⟨i, (hi | hi) | hi⟩)
    · exact Or.inl ⟨v, hv.symm⟩
    · exact Or.inr ⟨i, Or.inr ⟨false, hi⟩⟩
    · exact Or.inr ⟨i, Or.inl hi⟩
    · exact Or.inr ⟨i, Or.inr ⟨true, hi⟩⟩

end PoincareConjecture.M76.CutGraph
