import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.LocalBranchSourceComplex

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem ComponentBranchModel.exists_local_branch_inverses
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i)
    (L : SimplicialComplex ℝ (D.sample → ℝ × V3)) (hL : L.faces.Finite)
    (hLK : L.space ⊆ D.complex.space)
    {x y : E} (C : RawSourceCrossing e f S R x y)
    (hLC : MapsTo (fun z ↦ (D.inverse z : X)) L.space C.chart.source) :
    let branch (j : Bool) := if j then C.right else C.left
    let sheet (j : Bool) := L.space ∩
      {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) (if j then 1 else 0) = 0}
    ∃ (P : Bool → SimplicialComplex ℝ E) (u : ∀ j, sheet j ≃ₜ (P j).space),
      (∀ j, (P j).faces.Finite) ∧
      (∀ j, (P j).space = (S ∩ (D.graph ∘ f) ⁻¹' L.space) ∩ branch j) ∧
      (∀ j, (u j).IsFinitePL ∧ (u j).symm.IsFinitePL) ∧
      (∀ j (z : sheet j), f (u j z) = (D.inverse z : X) ∧ D.graph (f (u j z)) = z) ∧
      (∀ j (a : (P j).space), ((u j).symm a : D.sample → ℝ × V3) = D.graph (f a)) ∧
      (P false).space ∪ (P true).space = S ∩ (D.graph ∘ f) ⁻¹' L.space := by
  classical
  dsimp only
  let branch (j : Bool) := if j then C.right else C.left
  let sheet (j : Bool) := L.space ∩
    {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) (if j then 1 else 0) = 0}
  obtain ⟨T, hT, hTs⟩ := finitePL_exists_source_complex D.source_PL L hL
  have hTsource : T.space = S ∩ (D.graph ∘ f) ⁻¹' L.space := by
    rw [hTs, D.source_space]
    apply Subset.antisymm
    · intro a ha
      exact ⟨ha.1.1, ha.2⟩
    intro a ha
    have hmodel := D.graph_inverse ((D.graph ∘ f) a) (hLK ha.2)
    have hfx : (D.inverse ((D.graph ∘ f) a) : X) = f a :=
      D.graph_separates _ (D.inverse _).property _ hmodel
    exact ⟨⟨ha.1, show f a ∈ D.core from hfx ▸ (D.inverse _).property⟩, ha.2⟩
  have hTD : T.space ⊆ S := hTsource.subset.trans inter_subset_left
  have hTC : MapsTo f T.space C.chart.source := by
    intro a ha
    have haL := (hTsource.subset ha).2
    have hmodel := D.graph_inverse ((D.graph ∘ f) a) (hLK haL)
    have hfx : (D.inverse ((D.graph ∘ f) a) : X) = f a :=
      D.graph_separates _ (D.inverse _).property _ hmodel
    exact hfx ▸ hLC haL
  have hspaces := C.vertexSubcomplex_space T hTD hTC
  let P (j : Bool) := T.vertexSubcomplex (branch j)
  have hP (j : Bool) : (P j).faces.Finite := T.vertexSubcomplex_finite _ hT
  have hPs (j : Bool) : (P j).space = T.space ∩ branch j := by
    cases j
    · exact hspaces.1
    · exact hspaces.2
  have hPsource (j : Bool) : (P j).space ⊆ D.source.space :=
    ((hPs j).subset.trans inter_subset_left).trans (hTs.subset.trans inter_subset_left)
  have hPPL (j : Bool) : FinitePiecewiseAffineOn (D.graph ∘ f) (P j).space :=
    D.source_PL.restrict (P j) (hP j) (hPsource j)
  have hbranchInj (j : Bool) : InjOn f (branch j) := by
    cases j
    · intro a ha b hb hab
      exact congrArg Subtype.val (C.left_embedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    · intro a ha b hb hab
      exact congrArg Subtype.val (C.right_embedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hPInj (j : Bool) : InjOn (D.graph ∘ f) (P j).space := by
    intro a ha b hb hab
    exact hbranchInj j ((hPs j).subset ha).2 ((hPs j).subset hb).2
      (D.graph_separates (f a) (D.source_space.subset (hPsource j ha)).2 (f b) hab)
  have hbranchImage (j : Bool) (z : X) (hz : z ∈ C.chart.source) :
      z ∈ f '' branch j ↔ z ∈ R ∧ C.chart z (if j then 1 else 0) = 0 := by
    cases j
    · exact (C.left_image z hz).trans and_comm
    · exact (C.right_image z hz).trans and_comm
  have hbranchD (j : Bool) : branch j ⊆ S := by
    cases j
    · exact C.left_subset
    · exact C.right_subset
  have hPimage (j : Bool) : (D.graph ∘ f) '' (P j).space = sheet j := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haT := ((hPs j).subset ha).1
      have haL := (hTsource.subset haT).2
      have hfx : (D.inverse ((D.graph ∘ f) a) : X) = f a :=
        D.graph_separates _ (D.inverse _).property _ (D.graph_inverse _ (hLK haL))
      refine ⟨haL, (hbranchImage j _ (hLC haL)).mp ?_⟩
      exact ⟨a, ((hPs j).subset ha).2, hfx.symm⟩
    · rintro ⟨hzL, hz⟩
      obtain ⟨a, ha, haf⟩ := (hbranchImage j _ (hLC hzL)).mpr hz
      have hgraph : D.graph (f a) = z := (congrArg D.graph haf).trans (D.graph_inverse z (hLK hzL))
      exact ⟨a, (hPs j).symm.subset ⟨hTsource.symm.subset
        ⟨hbranchD j ha, show D.graph (f a) ∈ L.space from hgraph.symm ▸ hzL⟩, ha⟩, hgraph⟩
  have hex (j : Bool) : ∃ q : (P j).space ≃ₜ sheet j,
      q.IsFinitePL ∧ ∀ a : (P j).space, (q a : D.sample → ℝ × V3) = D.graph (f a) := by
    obtain ⟨q, hq, hqval⟩ := (hPPL j).exists_homeomorph_image (hPInj j)
    exact ⟨q.trans (Homeomorph.setCongr (hPimage j)),
      hq.setCongr rfl (hPimage j), hqval⟩
  choose q hq hqval using hex
  let u (j : Bool) := (q j).symm
  refine ⟨P, u, hP, fun j => (hPs j).trans (congrArg (fun s => s ∩ branch j) hTsource),
    fun j => ⟨(hq j).symm, hq j⟩, ?_, hqval, ?_⟩
  · intro j z
    have hgraph : D.graph (f (u j z)) = z := by
      rw [← hqval j, Homeomorph.apply_symm_apply]
    refine ⟨?_, hgraph⟩
    exact (D.graph_separates (D.inverse z) (D.inverse z).property (f (u j z))
      ((D.graph_inverse z (hLK z.property.1)).trans hgraph.symm)).symm
  · rw [hPs false, hPs true, ← inter_union_distrib_left]
    apply Subset.antisymm
    · exact fun a ha => hTsource.subset ha.1
    · intro a ha
      have haT := hTsource.symm.subset ha
      exact ⟨haT, C.whole_preimage.subset ⟨hTD haT, hTC haT⟩⟩

theorem ComponentBranchModel.exists_star_branch_inverses
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      let branch (j : Bool) := if j then C.right else C.left
      let sheet (j : Bool) := (D.complex.closedStar p).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) (if j then 1 else 0) = 0}
      ∃ (P : Bool → SimplicialComplex ℝ E) (u : ∀ j, sheet j ≃ₜ (P j).space),
        (∀ j, (P j).faces.Finite) ∧
        (∀ j, (P j).space =
          (S ∩ (D.graph ∘ f) ⁻¹' (D.complex.closedStar p).space) ∩ branch j) ∧
        (∀ j, (u j).IsFinitePL ∧ (u j).symm.IsFinitePL) ∧
        (∀ j (z : sheet j), f (u j z) = (D.inverse z : X) ∧ D.graph (f (u j z)) = z) ∧
        (∀ j (a : (P j).space), ((u j).symm a : D.sample → ℝ × V3) = D.graph (f a)) ∧
        (P false).space ∪ (P true).space =
          S ∩ (D.graph ∘ f) ⁻¹' (D.complex.closedStar p).space := by
  obtain ⟨x, y, C, hmap, hface, _⟩ := D.exists_raw_star p hp
  refine ⟨x, y, C, hmap, hface, ?_⟩
  exact D.exists_local_branch_inverses (D.complex.closedStar p)
    (SimplicialComplex.finite_closedStar_faces D.complex_finite p)
    (SimplicialComplex.space_subset_of_le (fun _ ht => ht.1)) C hmap

end PoincareConjecture.M76.Dehn.Annuli
