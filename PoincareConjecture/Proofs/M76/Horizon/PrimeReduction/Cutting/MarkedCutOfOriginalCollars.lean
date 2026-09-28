import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CenteredCollarRawMarks








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_marked_sphere_cut_of_original_collars
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (E : κ → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hSinside : ∀ i, S i ⊆ interior R) (hR : IsCompact R)
    (N : ∀ i, SimplicialComplex ℝ (E i)) (hN : ∀ i, (N i).faces.Finite)
    (HB : ∀ i, (N i).space ≃ₜ S i) (c : ∀ i, E i × ℝ → X)
    (hc : ∀ i, PolyhedralPLInCharts e (c i) ((N i).space ×ˢ Icc (-1 : ℝ) 1))
    (hi : ∀ i, Topology.IsEmbedding
      (fun z : ((N i).space ×ˢ Icc (-1 : ℝ) 1 : Set (E i × ℝ)) => c i z))
    (hcenter : ∀ i (x : (N i).space), c i ((x : E i), 0) = HB i x)
    (ε : κ → ℝ) (hε : ∀ i, 0 < ε i) (hεle : ∀ i, ε i ≤ 1)
    (hopen : ∀ i, IsOpen (c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))))
    (hinside : ∀ i, c i '' ((N i).space ×ˢ Icc (-ε i) (ε i)) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint
      (c i '' ((N i).space ×ˢ Icc (-ε i) (ε i)))
      (c j '' ((N j).space ×ˢ Icc (-ε j) (ε j))))
    (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hH : ∀ b (x : S b.1), (H b x : X) =
      c b.1 (((HB b.1).symm x : E b.1), if b.2 then ε b.1 else -ε b.1))
    (hBdis : Pairwise fun b d => Disjoint (B b) (B d))
    (hPL : PLDomain e (R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))))
    (hfront : frontier (R \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))) =
      frontier R ∪ ⋃ b, B b) :
    ∃ d : MarkedSphereCut e R κ,
      d.spheres = S ∧ d.collar = (fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))) ∧
      d.ports = B ∧ HEq d.portMap H := by
  classical
  let O : κ → Set X := fun i => c i '' ((N i).space ×ˢ Ioo (-ε i) (ε i))
  have hcompact (i : κ) : IsCompact (N i).space := (N i).isCompact_space_of_finite (hN i)
  have hclosure (i : κ) : closure (O i) = c i '' ((N i).space ×ˢ Icc (-ε i) (ε i)) :=
    (hc i).continuousOn.closure_image_collar_strip (hcompact i) (hε i) (hεle i)
  have hclInside (i : κ) : closure (O i) ⊆ interior R := (hclosure i).subset.trans (hinside i)
  have hclDis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)) := by
    intro i j hij
    rw [hclosure i, hclosure j]
    exact hdis hij
  have hzero (i : κ) : S i = c i '' ((N i).space ×ˢ ({0} : Set ℝ)) := by
    apply Subset.antisymm
    · intro x hx
      let z := (HB i).symm ⟨x, hx⟩
      exact ⟨((z : E i), 0), ⟨z.property, rfl⟩,
        (hcenter i z).trans (congrArg Subtype.val ((HB i).apply_symm_apply ⟨x, hx⟩))⟩
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      rw [ht0, hcenter i ⟨z, hz⟩]
      exact (HB i ⟨z, hz⟩).property
  have hinj (i : κ) : InjOn (c i) ((N i).space ×ˢ Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val ((hi i).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hproducts (i : κ) : ∃ W : (S i × unitInterval) ≃ₜ closure (O i),
      (∀ z, (W z : X) = c i (((HB i).symm z.1 : E i), (2 * (z.2 : ℝ) - 1) * ε i)) ∧
      (∀ z, (W z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ z, (W z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2) ∧ S i ⊆ closure (O i) := by
    obtain ⟨W, hW, hWo, hWs, hSc⟩ := exists_centered_collar_raw_marks
      (hcompact i) (c i) (hc i).continuousOn (hinj i) (hε i) (hεle i) (hzero i)
    exact ⟨((HB i).symm.prodCongr (Homeomorph.refl unitInterval)).trans W,
      fun z => hW _, fun z => hWo _, fun z => hWs _, hSc⟩
  choose W hW hWo hWs hSc using hproducts
  have hBimage (b : κ × Bool) : B b = c b.1 '' ((N b.1).space ×ˢ
      ({if b.2 then ε b.1 else -ε b.1} : Set ℝ)) := by
    apply Subset.antisymm
    · intro x hx
      let z := (H b).symm ⟨x, hx⟩
      exact ⟨(((HB b.1).symm z : E b.1), if b.2 then ε b.1 else -ε b.1),
        ⟨((HB b.1).symm z).property, rfl⟩,
        (hH b z).symm.trans (congrArg Subtype.val ((H b).apply_symm_apply ⟨x, hx⟩))⟩
    · rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht' : t = if b.2 then ε b.1 else -ε b.1 := ht
      have hv := hH b (HB b.1 ⟨z, hz⟩)
      rw [(HB b.1).symm_apply_apply] at hv
      rw [ht', ← hv]
      exact (H b (HB b.1 ⟨z, hz⟩)).property
  have hOfront (i : κ) : frontier (O i) = B (i, false) ∪ B (i, true) := by
    rw [hBimage, hBimage]
    exact (hi i).frontier_image_collar_strip (hcompact i) (hε i) (hεle i) (hopen i)
  obtain ⟨hQ, _, _, hcontact, _⟩ := finite_collar_cut_geometry hR hopen hclInside hclDis
  have hBcl (b : κ × Bool) : B b ⊆ closure (O b.1) := by
    intro x hx
    apply frontier_subset_closure ((hOfront b.1).symm.subset _)
    rcases b with ⟨i, b⟩
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hend (i : κ) (x : S i) :
      (W i (x, 0) : X) = H (i, false) x ∧ (W i (x, 1) : X) = H (i, true) x := by
    constructor <;> rw [hW, hH] <;> norm_num
  have hmid (i : κ) (x : S i) :
      (W i (x, ⟨(1/2 : ℝ), by norm_num⟩) : X) = x := by
    rw [hW]
    norm_num only [zero_mul]
    rw [hcenter]
    exact congrArg Subtype.val ((HB i).apply_symm_apply x)
  refine ⟨{
    spheres := S
    spherePL := sS
    sphereInterior := hSinside
    sphereDisjoint := hSdis
    collar := O
    product := W
    collarOpen := hopen
    collarInterior := hclInside
    collarDisjoint := hclDis
    openCoordinates := hWo
    centerCoordinates := hWs
    sphereClosure := hSc
    ports := B
    portMap := H
    portPL := sB
    portDisjoint := hBdis
    portClosure := hBcl
    collarContact := fun i => (hcontact i).trans (hOfront i)
    endpoints := hend
    center := hmid
    compactCut := hQ
    plCut := hPL
    frontierCut := hfront }, rfl, rfl, rfl, ?_⟩
  rfl

end PoincareConjecture.M76
