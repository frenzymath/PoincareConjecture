import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Map









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem disjoint_contractible_map_properties
    {X : Type*} [TopologicalSpace X]
    (J : SimplicialComplex ℝ P2) (_hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d : ℝ} (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : ∀ k, closure (B k).outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure (B 0).outer.inside) (closure (B 1).outer.inside))
    (H : closure (B 0).inner.inside ≃ₜ closure (B 1).inner.inside)
    (hHb : ∀ x : closure (B 0).inner.inside,
      (H x : P2) ∈ (B 1).inner.boundary ℝ ↔ (x : P2) ∈ (B 0).inner.boundary ℝ)
    (f g : P2 → X) (a : Fin 2 → P2 → X) (W R : Set X)
    (ha : ∀ k, Function.Injective (fun p : squareAnnulus L d ↦ a k p))
    (haW : ∀ k, a k '' squareAnnulus L d ⊆ W)
    (hadis : Disjoint (a 0 '' squareAnnulus L d) (a 1 '' squareAnnulus L d))
    (hkeep0 : ∀ x : closure (B 0).inner.inside, g (H x) = f x)
    (hkeep1 : ∀ x : closure (B 1).inner.inside, g (H.symm x) = f x)
    (hout : EqOn g f (J.space \ ((B 0).outer.inside ∪ (B 1).outer.inside)))
    (hcollar : ∀ k (p : squareAnnulus L d), g ((B k).chart p) = a k p)
    (hpreimage : J.space ∩ f ⁻¹' W = A 0 ∪ A 1)
    (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hW : W ⊆ interior R) :
    (∀ z ∈ A 0 ∪ A 1, ∀ w ∈ J.space, g w = g z → w = z) ∧
      MapsTo g J.space R ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) := by
  have hIint (k : Fin 2) : closure (B k).inner.inside ⊆ interior J.space :=
    (B k).nested.trans (subset_closure.trans (hcontract k))
  have hIsub (k : Fin 2) := (hIint k).trans interior_subset
  obtain ⟨hcover, _, _, _, _, _, _, ht0, ht1, hto⟩ :=
    disjoint_contractible_source_partition (B 0) (B 1)
      ((hcontract 0).trans interior_subset) ((hcontract 1).trans interior_subset) hdis
  have hgi0 (x : closure (B 0).inner.inside) : g x = f (H x) := by
    simpa only [Homeomorph.symm_apply_apply] using hkeep1 (H x)
  have hgi1 (x : closure (B 1).inner.inside) : g x = f (H.symm x) := by
    simpa only [Homeomorph.apply_symm_apply] using hkeep0 (H.symm x)
  have hcval (k : Fin 2) (x : A k) :
      ((B k).chart ((B k).chart.symm x) : P2) = x :=
    congrArg Subtype.val ((B k).chart.apply_symm_apply x)
  have hgW (k : Fin 2) (x : P2) (hx : x ∈ A k) : g x ∈ W := by
    change g (⟨x, hx⟩ : A k) ∈ W
    rw [← hcval k ⟨x, hx⟩, hcollar]
    exact haW k (mem_image_of_mem (a k) ((B k).chart.symm ⟨x, hx⟩).property)
  have hginj : InjOn g (A 0 ∪ A 1) := by
    intro x hx y hy heq
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, x ∈ A k := hx.elim (fun h ↦ ⟨0, h⟩) (fun h ↦ ⟨1, h⟩)
    obtain ⟨l, hl⟩ : ∃ l : Fin 2, y ∈ A l := hy.elim (fun h ↦ ⟨0, h⟩) (fun h ↦ ⟨1, h⟩)
    let p := (B k).chart.symm ⟨x, hk⟩
    let q := (B l).chart.symm ⟨y, hl⟩
    have hp : ((B k).chart p : P2) = x := hcval k ⟨x, hk⟩
    have hq : ((B l).chart q : P2) = y := hcval l ⟨y, hl⟩
    have he : a k p = a l q := by rw [← hcollar, ← hcollar, hp, hq]; exact heq
    by_cases hkl : k = l
    · subst l
      exact hp.symm.trans ((congrArg (fun v ↦ ((B k).chart v : P2)) (ha k he)).trans hq)
    · have hnot : Disjoint (a k '' squareAnnulus L d) (a l '' squareAnnulus L d) := by
        fin_cases k <;> fin_cases l
        · exact False.elim (hkl rfl)
        · exact hadis
        · exact hadis.symm
        · exact False.elim (hkl rfl)
      exact False.elim (disjoint_left.mp hnot ⟨p, p.property, rfl⟩ ⟨q, q.property, he.symm⟩)
  have hsingle : ∀ z ∈ A 0 ∪ A 1, ∀ w ∈ J.space, g w = g z → w = z := by
    intro z hz w hw heq
    have hzW : g z ∈ W := hz.elim (hgW 0 z) (hgW 1 z)
    have hwW : g w ∈ W := heq.symm ▸ hzW
    apply hginj _ hz heq
    rcases hcover.symm.subset hw with ((hwI | hwA) | (hwI | hwA)) | hwO
    · rw [hgi0 ⟨w, hwI⟩] at hwW
      have hbd := ht1.subset ⟨hpreimage.subset ⟨hIsub 1 (H ⟨w, hwI⟩).property, hwW⟩,
        (H ⟨w, hwI⟩).property⟩
      exact Or.inl ((oriented_collar_boundary_subsets (B 0)).2 ((hHb ⟨w, hwI⟩).mp hbd))
    · exact Or.inl hwA
    · rw [hgi1 ⟨w, hwI⟩] at hwW
      have hbd := ht0.subset ⟨hpreimage.subset ⟨hIsub 0 (H.symm ⟨w, hwI⟩).property, hwW⟩,
        (H.symm ⟨w, hwI⟩).property⟩
      have hbd' := (hHb (H.symm ⟨w, hwI⟩)).mpr hbd
      rw [H.apply_symm_apply] at hbd'
      exact Or.inr ((oriented_collar_boundary_subsets (B 1)).2 hbd')
    · exact Or.inr hwA
    · rw [hout hwO] at hwW
      exact (hto.subset ⟨hpreimage.subset ⟨hwO.1, hwW⟩, hwO⟩).elim
        (fun h ↦ Or.inl ((oriented_collar_boundary_subsets (B 0)).1 h))
        (fun h ↦ Or.inr ((oriented_collar_boundary_subsets (B 1)).1 h))
  have hinc (k : Fin 2) : A k ⊆ interior J.space :=
    (B k).carrier.subset.trans (sdiff_subset.trans (hcontract k))
  refine ⟨hsingle, ?_, ?_⟩
  · intro x hx
    rcases hcover.symm.subset hx with ((hxI | hxA) | (hxI | hxA)) | hxO
    · rw [hgi0 ⟨x, hxI⟩]; exact hin (hIsub 1 (H ⟨x, hxI⟩).property)
    · exact interior_subset (hW (hgW 0 x hxA))
    · rw [hgi1 ⟨x, hxI⟩]; exact hin (hIsub 0 (H.symm ⟨x, hxI⟩).property)
    · exact interior_subset (hW (hgW 1 x hxA))
    · rw [hout hxO]; exact hin hxO.1
  · intro x hx
    rcases hcover.symm.subset hx with ((hxI | hxA) | (hxI | hxA)) | hxO
    · rw [hgi0 ⟨x, hxI⟩, hfront _ (hIsub 1 (H ⟨x, hxI⟩).property)]
      exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hIint 1 (H ⟨x, hxI⟩).property) h)
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hIint 0 hxI) h)
    · exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hW (hgW 0 x hxA)) h)
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hinc 0 hxA) h)
    · rw [hgi1 ⟨x, hxI⟩, hfront _ (hIsub 0 (H.symm ⟨x, hxI⟩).property)]
      exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hIint 0 (H.symm ⟨x, hxI⟩).property) h)
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hIint 1 hxI) h)
    · exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hW (hgW 1 x hxA)) h)
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hinc 1 hxA) h)
    · rw [hout hxO]; exact hfront x hxO.1

end PoincareConjecture.M76.Dehn.Annuli
