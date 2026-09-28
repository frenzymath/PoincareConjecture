import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OutermostProperArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem SurfaceIntersectionComponents.exists_outermost_disk
    {X : Type*} {K J q : Set P2} {p f : P2 → X}
    (M : SurfaceIntersectionComponents K J p f q)
    (hJ : IsFinitePLBallPair P2 J q)
    (harcs : ∀ i, IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ q))
    (hne : (J ∩ f ⁻¹' (p '' K)).Nonempty) :
    ∃ i, ∃ A U : Set P2, ∃ a b : P2,
      a ≠ b ∧ IsFinitePLBallPair P2 A (U ∪ M.pieces i) ∧
      IsFinitePLBallPair ℝ U {a,b} ∧
      IsFinitePLBallPair ℝ (M.pieces i) {a,b} ∧
      A ⊆ J ∧ A ∩ q = U ∧ U ∩ M.pieces i = {a,b} ∧
      A ∩ f ⁻¹' (p '' K) = M.pieces i ∧
      Disjoint (A \ (U ∪ M.pieces i)) (f ⁻¹' (p '' K)) := by
  classical
  let : DecidableEq P2 := fun _ _ => Classical.propDecidable _
  let := M.components_finite
  let := Fintype.ofFinite M.right.vertexAbstractComplex.edgeGraph.ConnectedComponent
  have hends : ∀ i, ∃ a b : P2, a ≠ b ∧ M.pieces i ∩ q = {a,b} :=
    fun i => (harcs i).exists_boundary_eq_pair
  choose a b hab hrim using hends
  have hsub (i) : M.pieces i ⊆ J := fun x hx =>
    (M.right_space.subset (M.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  have hproper (i) : M.pieces i \ {a i,b i} ⊆ J \ q := by
    intro x hx
    exact ⟨hsub i hx.1,fun hxq => hx.2 ((hrim i).subset ⟨hx.1,hxq⟩)⟩
  have ha (i) : a i ∈ q := ((hrim i).symm.subset (Or.inl rfl)).2
  have hb (i) : b i ∈ q := ((hrim i).symm.subset (Or.inr rfl)).2
  have hne' : (Finset.univ : Finset M.right.vertexAbstractComplex.edgeGraph.ConnectedComponent).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨i,_⟩ := mem_iUnion.mp (M.cover.subset (M.right_space.symm.subset hx))
    exact ⟨i,Finset.mem_univ i⟩
  obtain ⟨i,_,A,U,hA,hU,hAJ,hAq,hUW,hcontact,havoid⟩ :=
    exists_outermost_proper_arc_disk_with_contact Finset.univ M.pieces a b
      (fun i _ => (hrim i) ▸ harcs i) (fun i _ => hab i)
      (fun i _ j _ hij => M.disjoint hij) hJ
      (fun i _ => ha i) (fun i _ => hb i) (fun i _ => hproper i) hne'
  have hcover : (⋃ j ∈ (Finset.univ : Finset _),M.pieces j) = J ∩ f ⁻¹' (p '' K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,_,hxj⟩ := mem_iUnion₂.mp hx
      exact M.right_space.subset (M.cover.symm.subset (mem_iUnion.mpr ⟨j,hxj⟩))
    · intro hx
      obtain ⟨j,hxj⟩ := mem_iUnion.mp (M.cover.subset (M.right_space.symm.subset hx))
      exact mem_iUnion₂.mpr ⟨j,Finset.mem_univ j,hxj⟩
  have hfull : A ∩ f ⁻¹' (p '' K) = M.pieces i := by
    rw [hcover] at hcontact
    apply Subset.antisymm
    · exact fun x hx => hcontact.subset ⟨hx.1,hAJ hx.1,hx.2⟩
    · intro x hx
      have hh := hcontact.symm.subset hx
      exact ⟨hh.1,hh.2.2⟩
  refine ⟨i,A,U,a i,b i,hab i,hA,hU,(hrim i) ▸ harcs i,hAJ,hAq,hUW,hfull,?_⟩
  exact disjoint_left.mpr fun x hx hy => hx.2 (Or.inr (hfull.subset ⟨hx.1,hy⟩))

open Classical in
theorem exists_original_outermost_boundary_compression_disk
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {E S : Set X}
    {K J q : Set P2} {p f : P2 → X}
    (M : SurfaceIntersectionComponents K J p f q)
    (hJ : IsFinitePLBallPair P2 J q)
    (harcs : ∀ i, IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ q))
    (hf : PolyhedralPLInCharts e f J) (hfi : InjOn f J)
    (hfE : MapsTo f J E) (hfproper : ∀ x ∈ J, f x ∈ frontier E ↔ x ∈ q)
    (himage : p '' K = S ∩ E) (hne : (f '' J ∩ S).Nonempty) :
    ∃ i, ∃ A U : Set P2, ∃ a b : P2,
      a ≠ b ∧ IsFinitePLBallPair P2 A (U ∪ M.pieces i) ∧
      IsFinitePLBallPair ℝ U {a,b} ∧
      IsFinitePLBallPair ℝ (M.pieces i) {a,b} ∧ A ⊆ J ∧
      PolyhedralPLInCharts e f A ∧ InjOn f A ∧ f '' A ⊆ E ∧
      A ∩ q = U ∧ U ∩ M.pieces i = {a,b} ∧
      f '' A ∩ S = f '' M.pieces i ∧
      f '' A ∩ frontier E = f '' U ∧
      f '' (A \ (U ∪ M.pieces i)) ⊆ interior E \ S := by
  have hnonempty : (J ∩ f ⁻¹' (p '' K)).Nonempty := by
    obtain ⟨_,⟨x,hx,rfl⟩,hxS⟩ := hne
    exact ⟨x,hx,himage.symm.subset ⟨hxS,hfE hx⟩⟩
  obtain ⟨i,A,U,a,b,hab,hA,hU,hW,hAJ,hAq,hUW,hcontact,havoid⟩ :=
    M.exists_outermost_disk hJ harcs hnonempty
  have hPL : PolyhedralPLInCharts e f A := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hA
    simpa only [hLs] using hf.restrict_finite L hL (hLs.subset.trans hAJ)
  have hcontactS : ∀ x ∈ A, f x ∈ S ↔ x ∈ M.pieces i := by
    intro x hx
    constructor
    · exact fun h => hcontact.subset ⟨hx,himage.symm.subset ⟨h,hfE (hAJ hx)⟩⟩
    · exact fun h => (himage.subset (hcontact.symm.subset h).2).1
  refine ⟨i,A,U,a,b,hab,hA,hU,hW,hAJ,hPL,hfi.mono hAJ,
    image_subset_iff.mpr (fun _ hx => hfE (hAJ hx)),hAq,hUW,?_,?_,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x,hx,rfl⟩,hxS⟩
      exact ⟨x,(hcontactS x hx).mp hxS,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      have hxA := hA.1 (Or.inr hx)
      exact ⟨mem_image_of_mem f hxA,(hcontactS x hxA).mpr hx⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨x,hx,rfl⟩,hxF⟩
      exact ⟨x,hAq.subset ⟨hx,(hfproper x (hAJ hx)).mp hxF⟩,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      have hx' := hAq.symm.subset hx
      exact ⟨mem_image_of_mem f hx'.1,(hfproper x (hAJ hx'.1)).mpr hx'.2⟩
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨(mem_interior_iff_notMem_frontier (hfE (hAJ hx.1))).mpr ?_,?_⟩
    · intro hfr
      exact hx.2 (Or.inl (hAq.subset ⟨hx.1,(hfproper x (hAJ hx.1)).mp hfr⟩))
    · exact fun h => hx.2 (Or.inr ((hcontactS x hx.1).mp h))

end PoincareConjecture.M76
