import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.EdgeFaceIncidence
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.NormalArcEdgeContacts
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FiniteFaceCounts

/-!
# Degree two at the original tetrahedral edge contacts

Each endpoint is labeled by its actual original face and the interval in
that face. Exactly two such labels meet each physical edge contact. Both
the intervals and this incidence count are derived from normal face position.
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_normal_arc_families_with_tetrahedral_incidence
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {S : Set X}
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) S g s.1 (A s)) :
    ∃ (γ : K.FaceOfCard 3 → Type) (_ : ∀ s, Finite (γ s))
      (d r : ∀ s, γ s → Set V3),
      (∀ s, (Pairwise fun i j => Disjoint (d s i) (d s j)) ∧
        (Q s).symm '' (⋃ i, d s i) = S ∩ (g '' convexHull ℝ (s.1 : Set E)) ∧
        (⋃ i, d s i) ⊆ convexHull ℝ ((A s) '' (s.1 : Set E)) ∩ (Q s).target ∧
        ∀ i, IsFinitePLBallPair ℝ (d s i) (r s i) ∧
          r s i = d s i ∩ intrinsicFrontier ℝ
            (convexHull ℝ ((A s) '' (s.1 : Set E)))) ∧
      ∀ t ∈ K.faces, t.card = 4 → ∀ a ∈ K.faces, a ⊆ t → a.card = 2 →
        ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)), g x ∈ S →
          {j : (Σ s, γ s) | j.1.1 ⊆ t ∧ g x ∈ (Q j.1).symm '' r j.1 j.2}.ncard = 2 := by
  classical
  choose γ hγ d r hdis hphysical htarget harcs hcontacts using fun s =>
    (hposition s).exists_normal_arc_family_with_edge_contacts K g hgi s.2.1 s.2.2
      (Q s) (A s) (hmap s) (hA s)
  refine ⟨γ, hγ, d, r, fun s => ⟨hdis s, hphysical s, htarget s, harcs s⟩, ?_⟩
  intro t ht ht4 a ha hat ha2 x hx hxS
  obtain ⟨s, u, hsu, hsK, huK, has, hau, hst, hut, hs3, hu3, hfaces⟩ :=
    exists_two_physical_triangle_cofaces_at_edge_point K g hgi ha ht hat ha2 ht4 hx
  let s' : K.FaceOfCard 3 := ⟨s, hsK, hs3⟩
  let u' : K.FaceOfCard 3 := ⟨u, huK, hu3⟩
  have hximage : g x ∈ g '' convexHull ℝ (a : Set E) :=
    mem_image_of_mem g (intrinsicInterior_subset hx)
  obtain ⟨i, hi, hi_unique⟩ := (hcontacts s' a has ha2 (g x) hximage).mp hxS
  obtain ⟨j, hj, hj_unique⟩ := (hcontacts u' a hau ha2 (g x) hximage).mp hxS
  have hsource_s : g x ∈ (Q s').source :=
    hmap s' (convexHull_mono has (intrinsicInterior_subset hx))
  have hsource_u : g x ∈ (Q u').source :=
    hmap u' (convexHull_mono hau (intrinsicInterior_subset hx))
  have hi_phys : g x ∈ (Q s').symm '' r s' i :=
    ⟨Q s' (g x), hi, (Q s').left_inv hsource_s⟩
  have hj_phys : g x ∈ (Q u').symm '' r u' j :=
    ⟨Q u' (g x), hj, (Q u').left_inv hsource_u⟩
  apply Set.ncard_eq_two.mpr
  refine ⟨⟨s', i⟩, ⟨u', j⟩, ?_, ?_⟩
  · intro heq
    exact hsu (congrArg (fun z : Σ s, γ s => z.1.1) heq)
  · ext z
    constructor
    · rintro ⟨hzt, hz⟩
      have hxface : g x ∈ g '' convexHull ℝ (z.1.1 : Set E) := by
        obtain ⟨w, hw, hwx⟩ := hz
        exact ((hphysical z.1).subset
          ⟨w, mem_iUnion.mpr ⟨z.2, (harcs z.1 z.2).1.1 hw⟩, hwx⟩).2
      rcases (hfaces z.1.1 hzt z.1.2.2).mp hxface with hs | hu
      · have hzface : z.1 = s' := Subtype.ext hs
        obtain ⟨v, k⟩ := z
        dsimp only at hzface
        subst v
        have hk : k = i := by
          apply hi_unique
          obtain ⟨w, hw, hwx⟩ := hz
          have hwT := (htarget s' (mem_iUnion.mpr ⟨k, (harcs s' k).1.1 hw⟩)).2
          exact (show Q s' (g x) = w from hwx ▸ (Q s').right_inv hwT).symm ▸ hw
        exact Or.inl (by cases hk; rfl)
      · have hzface : z.1 = u' := Subtype.ext hu
        obtain ⟨v, k⟩ := z
        dsimp only at hzface
        subst v
        have hk : k = j := by
          apply hj_unique
          obtain ⟨w, hw, hwx⟩ := hz
          have hwT := (htarget u' (mem_iUnion.mpr ⟨k, (harcs u' k).1.1 hw⟩)).2
          exact (show Q u' (g x) = w from hwx ▸ (Q u').right_inv hwT).symm ▸ hw
        exact Or.inr (by cases hk; rfl)
    · rintro (rfl | rfl)
      · exact ⟨hst, hi_phys⟩
      · exact ⟨hut, hj_phys⟩

end PoincareMT.M76
