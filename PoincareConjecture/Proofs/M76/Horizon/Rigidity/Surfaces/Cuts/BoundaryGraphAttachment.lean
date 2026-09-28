import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.BoundaryHeightExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.FiniteSeparatedAttachments









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def heightGraph (g : E → F) (x : E) : E × F := (x, g x)

theorem heightGraph_injective (g : E → F) : Function.Injective (heightGraph g) :=
  fun _ _ h ↦ congrArg Prod.fst h

@[simp] theorem heightGraph_mem_image (g : E → F) (s : Set E) (x : E) :
    heightGraph g x ∈ heightGraph g '' s ↔ x ∈ s := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact heightGraph_injective g hyx ▸ hy
  · exact mem_image_of_mem (heightGraph g)

theorem heightGraph_finitePL {g : E → F} {s : Set E}
    (hg : FinitePiecewiseAffineOn g s) : FinitePiecewiseAffineOn (heightGraph g) s := by
  have hid : FinitePiecewiseAffineOn (id : E → E) s := by
    obtain ⟨K, hK, hKs, _⟩ := hg
    exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  exact hid.prod_mk hg

def graphAttachmentCarrier (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (s : Set (E × F)) (u : ι → Set E) : Set ((E × F) × (ι → ℝ)) :=
  separatedCarrier k s (fun i ↦ heightGraph (g i) '' u i) Finset.univ

def graphAttachmentRim (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (b : Set (E × F)) (r d : ι → Set E) (a z : ι → E) :
    Set ((E × F) × (ι → ℝ)) :=
  separatedRim k b (fun i ↦ heightGraph (g i) '' r i)
    (fun i ↦ heightGraph (g i) '' d i)
    (fun i ↦ heightGraph (g i) (a i)) (fun i ↦ heightGraph (g i) (z i)) Finset.univ

noncomputable def graphAttachmentSheet (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (i : ι) : E → (E × F) × (ι → ℝ) :=
  separatedSheet k i ∘ heightGraph (g i)

theorem graphAttachmentSheet_injective (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (i : ι) : Function.Injective (graphAttachmentSheet g k i) :=
  (separatedSheet_injective k i).comp (heightGraph_injective (g i))

theorem graphAttachment_projection_image (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (s : Set (E × F)) (u : ι → Set E) :
    (fun p : (E × F) × (ι → ℝ) ↦ p.1.1) '' graphAttachmentCarrier g k s u =
      Prod.fst '' s ∪ ⋃ i, u i := by
  change (Prod.fst ∘ Prod.fst) '' _ = _
  rw [image_comp, graphAttachmentCarrier, projection_separatedCarrier]
  simp only [image_union, image_iUnion, Finset.mem_univ, iUnion_true]
  congr 1
  apply iUnion_congr
  intro i
  rw [← image_comp]
  exact image_id _

open Classical in
theorem graphAttachment_projection_fiber (g : ι → E → F) (k : ι → (E × F) → ℝ)
    (s : Set (E × F)) (u : ι → Set E) (x : E) :
    graphAttachmentCarrier g k s u ∩ (fun p : (E × F) × (ι → ℝ) ↦ p.1.1) ⁻¹' {x} =
      zeroSheet '' (s ∩ Prod.fst ⁻¹' {x}) ∪
        ⋃ i, if x ∈ u i then {graphAttachmentSheet g k i x} else ∅ := by
  ext p
  constructor
  · rintro ⟨hp | hp, hpx⟩
    · obtain ⟨y, hy, rfl⟩ := hp
      exact Or.inl ⟨y, ⟨hy, hpx⟩, rfl⟩
    · obtain ⟨i, _, y, ⟨v, hv, rfl⟩, rfl⟩ := mem_iUnion₂.mp hp
      have hvx : v = x := hpx
      subst v
      exact Or.inr (mem_iUnion.mpr ⟨i, by
        simp only [if_pos hv, mem_singleton_iff, graphAttachmentSheet, Function.comp_apply]⟩)
  · rintro (⟨y, ⟨hy, hyx⟩, rfl⟩ | hp)
    · exact ⟨Or.inl ⟨y, hy, rfl⟩, hyx⟩
    · obtain ⟨i, hp⟩ := mem_iUnion.mp hp
      split_ifs at hp with hx
      · have hpe : p = graphAttachmentSheet g k i x := hp
        subst p
        exact ⟨Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, heightGraph (g i) x,
          mem_image_of_mem (heightGraph (g i)) hx, rfl⟩), rfl⟩
      · exact hp.elim

theorem graphAttachmentSheet_mem_rim_iff
    (g : ι → E → F) (k : ι → (E × F) → ℝ)
    {b : Set (E × F)} {u r d : ι → Set E} {a z : ι → E}
    (hru : ∀ i, r i ⊆ u i)
    (hz : ∀ i x, x ∈ u i → (k i (heightGraph (g i) x) = 0 ↔ x ∈ d i))
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' d i)
      (heightGraph (g j) '' d j)))
    (i : ι) {x : E} (hx : x ∈ r i) :
    graphAttachmentSheet g k i x ∈ graphAttachmentRim g k b r d a z ↔
      x ∈ d i → x = a i ∨ x = z i := by
  have hzero : ∀ i y, y ∈ heightGraph (g i) '' u i →
      (k i y = 0 ↔ y ∈ heightGraph (g i) '' d i) := by
    rintro j y ⟨v, hv, rfl⟩
    rw [heightGraph_mem_image]
    exact hz j v hv
  have hh := separatedSheet_mem_separatedRim_iff k (b := b)
    (a := fun i ↦ heightGraph (g i) (a i)) (z := fun i ↦ heightGraph (g i) (z i))
    (fun i ↦ image_mono (hru i)) hzero hdis Finset.univ (Finset.mem_univ i)
    (mem_image_of_mem (heightGraph (g i)) hx)
  simpa only [graphAttachmentSheet, Function.comp_apply, graphAttachmentRim,
    heightGraph_mem_image,
    (heightGraph_injective (g i)).eq_iff] using hh



theorem exists_boundary_graph_attachments
    {s b : Set (E × F)} {u r d : ι → Set E} {a z : ι → E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    (hu : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (u i) (r i))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a i, z i})
    (hdr : ∀ i, d i ⊆ r i) (haz : ∀ i, a i ≠ z i)
    (f : ι → E → F) (hf : ∀ i, FinitePiecewiseAffineOn (f i) (d i))
    (hdb : ∀ i, heightGraph (f i) '' d i ⊆ b)
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (f i) '' d i)
      (heightGraph (f j) '' d j))) :
    ∃ (g : ι → E → F) (k : ι → (E × F) → ℝ),
      (∀ i, FinitePiecewiseAffineOn (g i) (u i) ∧ EqOn (g i) (f i) (d i)) ∧
      (∀ i, FinitePiecewiseAffineOn (k i) (heightGraph (g i) '' u i)) ∧
      (∀ i x, x ∈ u i → k i (heightGraph (g i) x) ∈ Icc 0 1 ∧
        (k i (heightGraph (g i) x) = 0 ↔ x ∈ d i)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (graphAttachmentCarrier g k s u)
        (graphAttachmentRim g k b r d a z) ∧
      FinitePiecewiseAffineOn (fun p : (E × F) × (ι → ℝ) ↦ p.1.1)
        (graphAttachmentCarrier g k s u) ∧
      (fun p : (E × F) × (ι → ℝ) ↦ p.1.1) '' graphAttachmentCarrier g k s u =
        Prod.fst '' s ∪ ⋃ i, u i ∧
      ∀ i, FinitePiecewiseAffineOn (graphAttachmentSheet g k i) (u i) ∧
        EqOn (graphAttachmentSheet g k i) (zeroSheet ∘ heightGraph (f i)) (d i) ∧
        graphAttachmentSheet g k i '' u i ⊆ graphAttachmentCarrier g k s u := by
  classical
  choose g hg using fun i ↦ (hu i).exists_boundary_height_extension (hdr i) (hf i)
  have hgraph (i : ι) := heightGraph_finitePL (hg i).1
  have heq (i : ι) : heightGraph (g i) '' d i = heightGraph (f i) '' d i :=
    Set.image_congr (fun x hx ↦ Prod.ext rfl ((hg i).2 hx))
  have hpieces (i : ι) := (hu i).image (hgraph i) (heightGraph_injective (g i)).injOn
  have hinterval (i : ι) : IsFinitePLBallPair ℝ (heightGraph (g i) '' d i)
      {heightGraph (g i) (a i), heightGraph (g i) (z i)} := by
    have hgd : FinitePiecewiseAffineOn (g i) (d i) := (hf i).congr (hg i).2.symm
    simpa only [image_pair] using (hd i).image (heightGraph_finitePL hgd)
      (heightGraph_injective (g i)).injOn
  have hdb' : ∀ i, heightGraph (g i) '' d i ⊆ b := by
    intro i; rw [heq]; exact hdb i
  have hdis' : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' d i)
      (heightGraph (g j) '' d j)) := by
    intro i j hij; rw [heq, heq]; exact hdis hij
  obtain ⟨k, hk, hz, hball, hprojection, _⟩ := exists_separated_disks hs hpieces hinterval
    hdb' (fun i ↦ image_mono (hdr i))
    (fun i h ↦ haz i (heightGraph_injective (g i) h)) hdis'
  have hz' : ∀ i x, x ∈ u i → k i (heightGraph (g i) x) ∈ Icc 0 1 ∧
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ d i) := by
    intro i x hx
    simpa only [heightGraph_mem_image] using
      hz i _ (mem_image_of_mem (heightGraph (g i)) hx)
  refine ⟨g, k, hg, hk, hz', hball,
    hprojection.postcomp (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap,
    graphAttachment_projection_image g k s u, ?_⟩
  intro i
  have hsheet := (separatedSheet_finitePL k i (hk i)).comp (hgraph i)
    (fun x hx ↦ mem_image_of_mem (heightGraph (g i)) hx)
  refine ⟨hsheet, ?_, ?_⟩
  · intro x hx
    have hx0 := (hz' i x ((hdr i).trans (hu i).1 hx)).2.mpr hx
    have hxg : heightGraph (g i) x = heightGraph (f i) x := Prod.ext rfl ((hg i).2 hx)
    exact (separatedSheet_eq_zeroSheet_iff k i _ _).mpr ⟨hxg, hx0⟩
  · rintro p ⟨x, hx, rfl⟩
    exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, heightGraph (g i) x,
      mem_image_of_mem (heightGraph (g i)) hx, rfl⟩)

end PoincareConjecture.M76.OriginalTriangleCopies
