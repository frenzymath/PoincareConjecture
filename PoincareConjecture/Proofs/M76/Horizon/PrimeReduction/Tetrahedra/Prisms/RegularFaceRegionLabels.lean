import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalFaceEdgeGapFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Cutting.FiniteArcComponentCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalFaceArcModels
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem exists_exceptions_of_actual_rectangle_family
    {E κ : Type*} [TopologicalSpace E] [Finite κ] {F T : Set E}
    [Finite (ConnectedComponents (F \ T : Set E))]
    (M W Z : κ → Set E) (hMi : Function.Injective M)
    (hcut : ∀ k, M k ∩ T = W k ∪ Z k)
    (hcomp : ∀ k x, x ∈ M k \ (W k ∪ Z k) →
      connectedComponentIn (F \ T) x = M k \ (W k ∪ Z k) ∧
      closure (connectedComponentIn (F \ T) x) = M k)
    (hchart : ∀ k, ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M k,
      (∀ x, (G x : E) ∈ W k ↔ (x : ℝ × ℝ).2 = 0) ∧
      (∀ x, (G x : E) ∈ Z k ↔ (x : ℝ × ℝ).2 = 1))
    {n c : ℕ} (hcard : Nat.card κ + c = n) (hc : c ≤ 3)
    (hcount : Nat.card (ConnectedComponents (F \ T : Set E)) = n + 1) :
    ∃ exceptional : Set (ConnectedComponents (F \ T : Set E)),
      exceptional.Finite ∧ exceptional.ncard ≤ 4 ∧
      (∀ x : (F \ T : Set E), ConnectedComponents.mk x ∉ exceptional ↔
        ∃! k, (x : E) ∈ M k \ T) ∧
      (∀ k x, x ∈ M k \ T →
        x ∈ F \ T ∧ closure (connectedComponentIn (F \ T) x) = M k) := by
  classical
  choose G hGW hGZ using hchart
  let z : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    ⟨(1/2,1/2),by norm_num⟩
  let point : κ → E := fun k => G k z
  have hpoint (k : κ) : point k ∈ M k \ (W k ∪ Z k) := by
    refine ⟨(G k z).property,?_⟩
    rintro (hW | hZ)
    · have h := (hGW k z).mp hW
      norm_num [z] at h
    · have h := (hGZ k z).mp hZ
      norm_num [z] at h
  have hdiff (k : κ) : M k \ T = M k \ (W k ∪ Z k) := by
    rw [←hcut k]
    ext x
    simp only [mem_sdiff,mem_inter_iff]
    tauto
  have hpointT (k : κ) : point k ∈ F \ T :=
    connectedComponentIn_subset _ _ ((hcomp k _ (hpoint k)).1.symm.subset (hpoint k))
  let f : κ → ConnectedComponents (F \ T : Set E) :=
    fun k => ConnectedComponents.mk ⟨point k,hpointT k⟩
  have hcoe (x y : (F \ T : Set E)) :
      ConnectedComponents.mk x = ConnectedComponents.mk y ↔
        (x : E) ∈ connectedComponentIn (F \ T) y := by
    rw [ConnectedComponents.coe_eq_coe',connectedComponentIn_eq_image y.property]
    constructor
    · exact fun h => mem_image_of_mem Subtype.val h
    · rintro ⟨z,hz,he⟩
      have hzx : z = x := Subtype.ext he
      rwa [hzx] at hz
  have hfmem (x : (F \ T : Set E)) (k : κ) :
      ConnectedComponents.mk x = f k ↔ (x : E) ∈ M k \ T := by
    rw [hcoe x ⟨point k,hpointT k⟩,(hcomp k _ (hpoint k)).1,←hdiff k]
  have hactual (k : κ) (x : E) (hx : x ∈ M k \ T) :
      x ∈ F \ T ∧ closure (connectedComponentIn (F \ T) x) = M k := by
    have hx' := (hdiff k).subset hx
    exact ⟨connectedComponentIn_subset _ _ ((hcomp k x hx').1.symm.subset hx'),
      (hcomp k x hx').2⟩
  have hunique (x : E) (i j : κ) (hi : x ∈ M i \ T) (hj : x ∈ M j \ T) : i = j :=
    hMi ((hactual i x hi).2.symm.trans (hactual j x hj).2)
  have hfi : Function.Injective f := by
    intro i j he
    exact hunique (point i) i j ((hdiff i).symm.subset (hpoint i))
      ((hfmem ⟨point i,hpointT i⟩ j).mp he)
  let exceptional : Set (ConnectedComponents (F \ T : Set E)) := (range f)ᶜ
  have hbound : exceptional.ncard ≤ 4 := by
    have hsum := ncard_add_ncard_compl (range f)
    rw [ncard_range_of_injective hfi] at hsum
    change Nat.card κ + exceptional.ncard = Nat.card (ConnectedComponents (F \ T : Set E)) at hsum
    omega
  refine ⟨exceptional,toFinite _,hbound,?_,hactual⟩
  intro x
  constructor
  · intro hx
    have hxrange : ConnectedComponents.mk x ∈ range f := not_not.mp hx
    obtain ⟨k,hk⟩ := hxrange
    have hxk := (hfmem x k).mp hk.symm
    exact ⟨k,hxk,fun j hj => hunique x j k hj hxk⟩
  · rintro ⟨k,hk,_⟩ hx
    exact hx ⟨k,((hfmem x k).mpr hk).symm⟩



theorem exists_original_face_rectangle_exceptions
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] [Finite κ]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ convexHull ℝ (s : Set E))
    (hrim : ∀ i, r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (M W Z : κ → Set E) (hMi : Function.Injective M)
    (hcut : ∀ k, M k ∩ (⋃ i, d i) = W k ∪ Z k)
    (hcomp : ∀ k x, x ∈ M k \ (W k ∪ Z k) →
      connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x = M k \ (W k ∪ Z k) ∧
      closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x) = M k)
    (hchart : ∀ k, ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M k,
      (∀ x, (G x : E) ∈ W k ↔ (x : ℝ × ℝ).2 = 0) ∧
      (∀ x, (G x : E) ∈ Z k ↔ (x : ℝ × ℝ).2 = 1))
    {c : ℕ} (hcard : Nat.card κ + c = Nat.card ι) (hc : c ≤ 3) :
    ∃ exceptional : Set (ConnectedComponents (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E)),
      exceptional.Finite ∧ exceptional.ncard ≤ 4 ∧
      (∀ x : (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E), ConnectedComponents.mk x ∉ exceptional ↔
        ∃! k, (x : E) ∈ M k \ ⋃ i, d i) ∧
      (∀ k x, x ∈ M k \ ⋃ i, d i →
        x ∈ convexHull ℝ (s : Set E) \ ⋃ i, d i ∧
        closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x) = M k) := by
  classical
  choose p q hpq hpqr using fun i => (hd i).exists_boundary_eq_pair
  obtain ⟨hfinite,hcount,_⟩ := finite_proper_arc_component_count
    (isFinitePLBallPair_independent_triangle s (K.indep hs) hs3) d p q
    (fun i => hpqr i ▸ hd i) hpq hsub (fun i => (hpqr i).symm.trans (hrim i)) hdis
  let := hfinite
  exact exists_exceptions_of_actual_rectangle_family M W Z hMi hcut hcomp hchart hcard hc hcount

end PoincareConjecture.M76.PrismBelt
