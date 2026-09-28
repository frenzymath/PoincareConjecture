import PoincareConjecture.Proofs.M76.Mathlib.FinitePLTwoAttachedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedGraphGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem exists_finitePL_relative_region_gluing {ι : Type*} [Finite ι]
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
    (d u w : ι → Bool → Set E) (D U W : ι → Bool → Set F)
    (a b : ι → Bool → E) (A B : ι → Bool → F)
    (hd : ∀ i j, IsFinitePLBallPair (ℝ × ℝ) (d i j) (u i j ∪ w i j))
    (hds : ∀ i j, d i j ⊆ S i)
    (hD : ∀ i j, IsFinitePLBallPair (ℝ × ℝ) (D i j) (U i j ∪ W i j))
    (hDt : ∀ i j, D i j ⊆ T i)
    (hu : ∀ i j, IsFinitePLBallPair ℝ (u i j) {a i j, b i j})
    (huR : ∀ i j, u i j ⊆ R i)
    (hw : ∀ i j, IsFinitePLBallPair ℝ (w i j) {a i j, b i j})
    (hab : ∀ i j, a i j ≠ b i j)
    (hproper : ∀ i j, w i j \ {a i j, b i j} ⊆ S i \ R i)
    (hU : ∀ i j, IsFinitePLBallPair ℝ (U i j) {A i j, B i j})
    (hUQ : ∀ i j, U i j ⊆ Q i)
    (hW : ∀ i j, IsFinitePLBallPair ℝ (W i j) {A i j, B i j})
    (hAB : ∀ i j, A i j ≠ B i j)
    (hProper : ∀ i j, W i j \ {A i j, B i j} ⊆ T i \ Q i)
    (hdis : ∀ i, Disjoint (d i false) (d i true))
    (hDis : ∀ i, Disjoint (D i false) (D i true))
    (e : ∀ i j, d i j ≃ₜ D i j) (he : ∀ i j, (e i j).IsFinitePL)
    (hmemu : ∀ i j (x : d i j), (x : E) ∈ u i j ↔ (e i j x : F) ∈ U i j)
    (hmemw : ∀ i j (x : d i j), (x : E) ∈ w i j ↔ (e i j x : F) ∈ W i j)
    (hagree : ∀ i j (x : u i j),
      (G ⟨x, ((hSgraph i).symm.subset (huR i j x.property)).2⟩ : F) =
        e i j ⟨x, (hd i j).1 (Or.inl x.property)⟩) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i j (x : d i j),
        (H ⟨x, mem_iUnion.mpr ⟨i, hds i j x.property⟩⟩ : F) = e i j x) ∧
      (∀ x : g, H ⟨x, hgunion x.property⟩ = ⟨G x, hhunion (G x).property⟩) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      ∀ i j (x : ⋃ i, S i), (x : E) ∈ d i j ↔ (H x : F) ∈ D i j := by
  classical
  have hRg (i : ι) : R i ⊆ g := fun x hx => ((hSgraph i).symm.subset hx).2
  have hQh (i : ι) : Q i ⊆ h := fun x hx => ((hTgraph i).symm.subset hx).2
  have hex (i : ι) : ∃ f : S i ≃ₜ T i, f.IsFinitePL ∧
      (∀ j (x : d i j), f ⟨x, hds i j x.property⟩ =
        ⟨e i j x, hDt i j (e i j x).property⟩) ∧
      (∀ x : R i, (f ⟨x, (hS i).1 x.property⟩ : F) = G ⟨x, hRg i x.property⟩) ∧
      ∀ x : S i, (x : E) ∈ R i ↔ (f x : F) ∈ Q i := by
    have hcopy := hS i
    have hGcopy := hG
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ := hcopy
    obtain ⟨_, ⟨J, hJ, hJg, _⟩, _⟩ := hGcopy
    obtain ⟨L, hL, hLR⟩ := K.exists_finite_triangulation_inter J hK hJ
    rw [hKS, hJg, hSgraph i] at hLR
    let bnd := G.restrictSubsets (hRg i) (hQh i) (hGmem i)
    have hbnd : bnd.IsFinitePL :=
      hG.restrictSubsets (hRg i) (hQh i) (hGmem i) L hL hLR
    obtain ⟨f, hf, hfd, hfr, _, hfmem⟩ :=
      (hS i).exists_extension_of_two_attached_disks_and_boundary (hT i)
        (d i) (u i) (w i) (D i) (U i) (W i) (a i) (b i) (A i) (B i)
        (hd i) (hds i) (hD i) (hDt i)
        (hu i) (huR i) (hw i) (hab i) (hproper i)
        (hU i) (hUQ i) (hW i) (hAB i) (hProper i)
        (hdis i) (hDis i) (e i) (he i) (hmemu i) (hmemw i)
        bnd hbnd (hagree i)
    exact ⟨f, hf, hfd, fun x => congrArg (fun y : T i => (y : F)) (hfr x), hfmem⟩
  choose f hf hfd hfr hfmem using hex
  obtain ⟨H, hH, hHf, hHG, hpieces⟩ :=
    exists_finitePL_region_gluing_of_graph S R T Q hSgraph hTgraph hSpair hTpair
      hgunion hhunion G hGmem f hf hfmem hfr
  have hkeep (i : ι) (j : Bool) (x : d i j) :
      (H ⟨x, mem_iUnion.mpr ⟨i, hds i j x.property⟩⟩ : F) = e i j x :=
    (hHf i ⟨x, hds i j x.property⟩).trans
      (congrArg (fun y : T i => (y : F)) (hfd i j x))
  refine ⟨H, hH, hkeep, hHG, hpieces, ?_⟩
  intro i j
  exact H.mem_subset_iff_of_extension (e i j)
    ((hds i j).trans (subset_iUnion S i)) ((hDt i j).trans (subset_iUnion T i))
    (fun x => Subtype.ext (hkeep i j x))

end Set
