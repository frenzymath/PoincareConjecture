import PoincareConjecture.Proofs.M02.SimplexGeometry
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Topology.CWComplex.Classical.Finite

set_option autoImplicit false

open Set Metric Topology

universe u

namespace PoincareConjecture.Proofs.M02

theorem exists_simplexCharacteristicMap_subtype {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hne : s.Nonempty) (hi : AffineIndependent ℝ ((↑) : s → E))
    (S : Set E) (hS : convexHull ℝ (s : Set E) ⊆ S) :
    ∃ e : PartialEquiv (Fin (s.card - 1) → ℝ) S,
      e.source = ball 0 1 ∧
      e.target = Subtype.val ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      ContinuousOn e (closedBall 0 1) ∧ ContinuousOn e.symm e.target ∧
      e '' closedBall 0 1 = Subtype.val ⁻¹' convexHull ℝ (s : Set E) ∧
      e '' sphere 0 1 = Subtype.val ⁻¹' intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨e, hsource, htarget, he, hinverse, hball, hsphere⟩ :=
    exists_simplexCharacteristicMap s hne hi
  obtain ⟨p, hp⟩ := hne
  let fallback : S := ⟨p, hS (subset_convexHull ℝ (s : Set E) hp)⟩
  let f : (Fin (s.card - 1) → ℝ) → S := fun x =>
    if hx : e x ∈ S then ⟨e x, hx⟩ else fallback
  have hf (x : Fin (s.card - 1) → ℝ) (hx : x ∈ closedBall 0 1) :
      (f x : E) = e x := by
    have hxS : e x ∈ S := hS (hball ▸ mem_image_of_mem e hx)
    simp only [f, dif_pos hxS]
  let restricted : PartialEquiv (Fin (s.card - 1) → ℝ) S := {
    toFun := f
    invFun := fun y => e.symm y.val
    source := ball 0 1
    target := Subtype.val ⁻¹' e.target
    map_source' := by
      intro x hx
      change (f x : E) ∈ e.target
      rw [hf x (ball_subset_closedBall hx)]
      exact e.map_source (hsource.symm ▸ hx)
    map_target' := by
      intro y hy
      exact hsource ▸ e.map_target hy
    left_inv' := by
      intro x hx
      rw [hf x (ball_subset_closedBall hx)]
      exact e.left_inv (hsource.symm ▸ hx)
    right_inv' := by
      intro y hy
      apply Subtype.ext
      rw [hf _ (ball_subset_closedBall (hsource ▸ e.map_target hy))]
      exact e.right_inv hy }
  have himage (B : Set (Fin (s.card - 1) → ℝ)) (hB : B ⊆ closedBall 0 1) :
      restricted '' B = Subtype.val ⁻¹' (e '' B) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hf x (hB hx)).symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext ((hf x (hB hx)).trans hxy)⟩
  refine ⟨restricted, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change Subtype.val ⁻¹' e.target = _
    rw [htarget]
  · apply IsEmbedding.subtypeVal.continuousOn_iff.mpr
    exact he.continuousOn.congr hf
  · exact hinverse.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
  · rw [himage _ Subset.rfl, hball]
  · rw [himage _ sphere_subset_closedBall, hsphere]

theorem exists_finite_simplicialCW {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hfinite : K.faces.Finite) :
    ∃ C : CWComplex (univ : Set K.space),
      letI := C
      CWComplex.Finite (univ : Set K.space) ∧
        ∀ n : ℕ, Nonempty (Topology.CWComplex.cell (univ : Set K.space) n ≃
          {s : K.faces // s.val.card = n + 1}) := by
  classical
  let : _root_.Finite K.faces := hfinite.to_subtype
  let cells : ℕ → Type u := fun n => {s : K.faces // s.val.card = n + 1}
  have hmaps (n : ℕ) (s : cells n) :
      ∃ e : PartialEquiv (Fin n → ℝ) K.space,
        e.source = ball 0 1 ∧
        e.target = Subtype.val ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s.val.val : Set E)) ∧
        ContinuousOn e (closedBall 0 1) ∧ ContinuousOn e.symm e.target ∧
        e '' closedBall 0 1 = Subtype.val ⁻¹' convexHull ℝ (s.val.val : Set E) ∧
        e '' sphere 0 1 = Subtype.val ⁻¹' intrinsicFrontier ℝ
          (convexHull ℝ (s.val.val : Set E)) := by
    rcases s with ⟨⟨s, hs⟩, hcard⟩
    change s.card = n + 1 at hcard
    have hdim : s.card - 1 = n := by omega
    subst n
    exact exists_simplexCharacteristicMap_subtype s
      (K.nonempty_of_mem_faces hs) (K.indep hs) K.space (K.convexHull_subset_space hs)
  choose f hsource htarget hcontinuous hinverse hclosed hboundary using hmaps
  have hfiniteCells (n : ℕ) : _root_.Finite (cells n) := inferInstance
  have hbounded : ∀ᶠ n in Filter.atTop, IsEmpty (cells n) := by
    obtain ⟨N, hN⟩ := (hfinite.image Finset.card).bddAbove
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ⟨fun s => ?_⟩⟩
    have hs := hN (mem_image_of_mem Finset.card s.val.property)
    have hc := s.property
    omega
  have hopen (n : ℕ) (s : cells n) : f n s '' ball 0 1 =
      Subtype.val ⁻¹' intrinsicInterior ℝ (convexHull ℝ (s.val.val : Set E)) := by
    rw [← hsource n s, (f n s).image_source_eq_target, htarget]

  have hseparate (s t : Finset E) (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hne : s ≠ t) :
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
        (intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hintersection : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
      rw [Finset.coe_inter]
      exact K.inter_subset_convexHull hs ht
        ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hy⟩
    by_cases hst : s ⊆ t
    · have hproper : s ∩ t ⊂ t := by
        rw [Finset.inter_eq_left.mpr hst]
        exact lt_of_le_of_ne hst hne
      exact Set.disjoint_left.mp (simplex_intrinsicInterior_disjoint_face t (s ∩ t)
        (K.nonempty_of_mem_faces ht) (K.indep ht) hproper) hy hintersection
    · have hproper : s ∩ t ⊂ s := by
        refine lt_of_le_of_ne Finset.inter_subset_left ?_
        intro heq
        exact hst (heq ▸ Finset.inter_subset_right)
      exact Set.disjoint_left.mp (simplex_intrinsicInterior_disjoint_face s (s ∩ t)
        (K.nonempty_of_mem_faces hs) (K.indep hs) hproper) hx hintersection
  have hdisjoint : (univ : Set (Σ n, cells n)).PairwiseDisjoint
      (fun ni => f ni.1 ni.2 '' ball 0 1) := by
    intro ⟨n, s⟩ _ ⟨m, t⟩ _ hne
    change Disjoint (f n s '' ball 0 1) (f m t '' ball 0 1)
    rw [hopen, hopen]
    apply Disjoint.preimage
    apply hseparate _ _ s.val.property t.val.property
    intro heq
    have hface : s.val = t.val := Subtype.ext heq
    have hdim : n = m := by
      have hs := s.property
      have ht := t.property
      rw [hface] at hs
      omega
    subst m
    exact hne (congrArg (Sigma.mk n) (Subtype.ext hface))
  have hattach (n : ℕ) (s : cells n) : MapsTo (f n s) (sphere 0 1)
      (⋃ (m < n) (t : cells m), f m t '' closedBall 0 1) := by
    intro x hx
    have hfront : (f n s x : E) ∈ intrinsicFrontier ℝ (convexHull ℝ (s.val.val : Set E)) := by
      change f n s x ∈ Subtype.val ⁻¹' intrinsicFrontier ℝ _
      rw [← hboundary]
      exact mem_image_of_mem (f n s) hx
    rw [simplex_intrinsicFrontier s.val.val
      (K.nonempty_of_mem_faces s.val.property) (K.indep s.val.property)] at hfront
    obtain ⟨i, hi⟩ := mem_iUnion.mp hfront
    let t := s.val.val.erase (i : E)
    have ht : t.Nonempty := Finset.coe_nonempty.mp
      (convexHull_nonempty_iff.mp ⟨_, hi⟩)
    have htface : t ∈ K.faces := K.down_closed s.val.property (Finset.erase_subset _ _) ht
    have hcard : t.card = n := by
      dsimp only [t]
      rw [Finset.card_erase_of_mem i.property, s.property, Nat.add_sub_cancel]
    have hn : 0 < n := by
      have := Finset.card_pos.mpr ht
      omega
    let lower : cells (n - 1) := ⟨⟨t, htface⟩, by dsimp; omega⟩
    refine mem_iUnion.mpr ⟨n - 1, mem_iUnion.mpr ⟨by omega,
      mem_iUnion.mpr ⟨lower, ?_⟩⟩⟩
    rw [hclosed]
    exact hi
  have hcover : ⋃ (n : ℕ) (s : cells n), f n s '' closedBall 0 1 =
      (univ : Set K.space) := by
    apply Subset.antisymm (subset_univ _)
    intro x _
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.property
    let cell : cells (s.card - 1) := ⟨⟨s, hs⟩,
      (Nat.sub_add_cancel (Finset.one_le_card.mpr (K.nonempty_of_mem_faces hs))).symm⟩
    refine mem_iUnion.mpr ⟨s.card - 1, mem_iUnion.mpr ⟨cell, ?_⟩⟩
    rw [hclosed]
    exact hx
  let C := CWComplex.mkFinite univ cells f hbounded hfiniteCells hsource hcontinuous hinverse
    hdisjoint hattach hcover
  refine ⟨C, ?_, fun n => ⟨Equiv.refl _⟩⟩
  exact CWComplex.finite_mkFinite univ cells f hbounded hfiniteCells hsource hcontinuous hinverse
    hdisjoint hattach hcover

end PoincareConjecture.Proofs.M02
