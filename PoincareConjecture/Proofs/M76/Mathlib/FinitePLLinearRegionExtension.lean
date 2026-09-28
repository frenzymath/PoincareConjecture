import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRelativeRegionGluing
import PoincareConjecture.Proofs.M76.Mathlib.LinearPatchHomeomorphisms

set_option autoImplicit false

open Set

namespace Set

theorem proper_attachment_of_graph_contact {X : Type*}
    {S R d u w v g : Set X} (hS : S ∩ g = R) (hds : d ⊆ S)
    (hd : d ∩ g = u) (hwd : w ⊆ d) (huw : u ∩ w = v) :
    u ⊆ R ∧ w \ v ⊆ S \ R := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have h := hd.symm.subset hx
    exact hS.subset ⟨hds h.1, h.2⟩
  · intro x hx
    refine ⟨hds (hwd hx.1), ?_⟩
    intro hxR
    have hxg := (hS.symm.subset hxR).2
    exact hx.2 (huw.subset ⟨hd.subset ⟨hwd hx.1, hxg⟩, hx.1⟩)

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finitePL_linear_region_gluing {ι : Type*} [Finite ι]
    (S R : ι → Set E) (T Q : ι → Set F)
    (hS : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (S i) (R i))
    (hT : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (T i) (Q i))
    {g : Set E} {h : Set F}
    (hSgraph : ∀ i, S i ∩ g = R i) (hTgraph : ∀ i, T i ∩ h = Q i)
    (hSpair : Pairwise (fun i j => S i ∩ S j ⊆ g))
    (hTpair : Pairwise (fun i j => T i ∩ T j ⊆ h))
    (hgunion : g ⊆ ⋃ i, S i) (hhunion : h ⊆ ⋃ i, T i)
    (G : g ≃ₜ h) (hG : G.IsFinitePL)
    (hGmem : ∀ i (x : g), (x : E) ∈ R i ↔ (G x : F) ∈ Q i)
    (d u w : ι → Bool → Set E) (a b : ι → Bool → E)
    (L : Bool → E ≃L[ℝ] F)
    (hd : ∀ i j, IsFinitePLBallPair (ℝ × ℝ) (d i j) (u i j ∪ w i j))
    (hds : ∀ i j, d i j ⊆ S i)
    (hDt : ∀ i j, L j '' d i j ⊆ T i)
    (hu : ∀ i j, IsFinitePLBallPair ℝ (u i j) {a i j, b i j})
    (hw : ∀ i j, IsFinitePLBallPair ℝ (w i j) {a i j, b i j})
    (hab : ∀ i j, a i j ≠ b i j)
    (hcorner : ∀ i j, u i j ∩ w i j = {a i j, b i j})
    (hdgraph : ∀ i j, d i j ∩ g = u i j)
    (hDgraph : ∀ i j, (L j '' d i j) ∩ h = L j '' u i j)
    (hdis : ∀ i, Disjoint (d i false) (d i true))
    (hDis : ∀ i, Disjoint (L false '' d i false) (L true '' d i true))
    (hGL : ∀ i j (x : u i j),
      (G ⟨x, ((hdgraph i j).symm.subset x.property).2⟩ : F) = L j x) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i j (x : d i j),
        (H ⟨x, mem_iUnion.mpr ⟨i, hds i j x.property⟩⟩ : F) = L j x) ∧
      (∀ x : g, H ⟨x, hgunion x.property⟩ = ⟨G x, hhunion (G x).property⟩) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      ∀ i j (x : ⋃ i, S i), (x : E) ∈ d i j ↔ (H x : F) ∈ L j '' d i j := by
  let D : ι → Bool → Set F := fun i j => L j '' d i j
  let U : ι → Bool → Set F := fun i j => L j '' u i j
  let W : ι → Bool → Set F := fun i j => L j '' w i j
  let A : ι → Bool → F := fun i j => L j (a i j)
  let B : ι → Bool → F := fun i j => L j (b i j)
  let e : ∀ i j, d i j ≃ₜ D i j := fun i j => (L j).toHomeomorph.image (d i j)
  have hD (i : ι) (j : Bool) : IsFinitePLBallPair (ℝ × ℝ) (D i j) (U i j ∪ W i j) := by
    simpa only [D, U, W, image_union] using ((hd i j).linear_image_patch_data (L j)).1
  have hU (i : ι) (j : Bool) : IsFinitePLBallPair ℝ (U i j) {A i j, B i j} := by
    simpa only [U, A, B, image_pair] using ((hu i j).linear_image_patch_data (L j)).1
  have hW (i : ι) (j : Bool) : IsFinitePLBallPair ℝ (W i j) {A i j, B i j} := by
    simpa only [W, A, B, image_pair] using ((hw i j).linear_image_patch_data (L j)).1
  have hAB (i : ι) (j : Bool) : A i j ≠ B i j := fun h => hab i j ((L j).injective h)
  have he (i : ι) (j : Bool) : (e i j).IsFinitePL :=
    ((hd i j).linear_image_patch_data (L j)).2.1
  have hwd (i : ι) (j : Bool) : w i j ⊆ d i j := fun _ hx => (hd i j).1 (Or.inr hx)
  have hAttach (i : ι) (j : Bool) :
      u i j ⊆ R i ∧ w i j \ {a i j, b i j} ⊆ S i \ R i :=
    proper_attachment_of_graph_contact (hSgraph i) (hds i j)
      (hdgraph i j) (hwd i j) (hcorner i j)
  have hTargetCorner (i : ι) (j : Bool) : U i j ∩ W i j = {A i j, B i j} := by
    dsimp only [U, W, A, B]
    rw [← image_inter (L j).injective, hcorner i j, image_pair]
  have hTargetAttach (i : ι) (j : Bool) :
      U i j ⊆ Q i ∧ W i j \ {A i j, B i j} ⊆ T i \ Q i :=
    proper_attachment_of_graph_contact (hTgraph i) (hDt i j)
      (hDgraph i j) (image_mono (hwd i j)) (hTargetCorner i j)
  have hmemu (i : ι) (j : Bool) (x : d i j) :
      (x : E) ∈ u i j ↔ (e i j x : F) ∈ U i j :=
    ((hd i j).linear_image_patch_data (L j)).2.2.2.1 (u i j) x
  have hmemw (i : ι) (j : Bool) (x : d i j) :
      (x : E) ∈ w i j ↔ (e i j x : F) ∈ W i j :=
    ((hd i j).linear_image_patch_data (L j)).2.2.2.1 (w i j) x
  obtain ⟨H, hH, hkeep, hgraph, hregions, hpatches⟩ :=
    exists_finitePL_relative_region_gluing S R T Q hS hT hSgraph hTgraph
      hSpair hTpair hgunion hhunion G hG hGmem d u w D U W a b A B
      hd hds hD hDt hu (fun i j => (hAttach i j).1) hw hab
      (fun i j => (hAttach i j).2) hU (fun i j => (hTargetAttach i j).1)
      hW hAB (fun i j => (hTargetAttach i j).2)
      hdis hDis e he hmemu hmemw hGL
  exact ⟨H, hH, hkeep, hgraph, hregions, hpatches⟩

end Set
