import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.PulledBackAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOriginalAtlasGluing

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem partial_pullback_chart_transition
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (M : OpenPartialHomeomorph X Y) (hM : M.target = univ)
    (a b : OpenPartialHomeomorph Y V3) :
    (M.trans a).symm.trans (M.trans b) = a.symm.trans b := by
  have ht (y : Y) : y ∈ M.target := hM.symm ▸ mem_univ y
  apply OpenPartialHomeomorph.ext
  · intro z
    change b (M (M.symm (a.symm z))) = b (a.symm z)
    rw [M.right_inv (ht _)]
  · intro z
    change a (M (M.symm (b.symm z))) = a (b.symm z)
    rw [M.right_inv (ht _)]
  · ext z
    change (z ∈ a.target ∧ a.symm z ∈ M.target) ∧
      M.symm (a.symm z) ∈ M.source ∧ M (M.symm (a.symm z)) ∈ b.source ↔ _
    rw [M.right_inv (ht _)]
    exact ⟨fun hz => ⟨hz.1.1,hz.2.2⟩,
      fun hz => ⟨⟨hz.1,ht _⟩,M.map_target (ht _),hz.2⟩⟩

theorem retained_partial_pullback_chart_transition
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (M : OpenPartialHomeomorph X W)
    (e : ι → OpenPartialHomeomorph X V3)
    (atlas : κ → OpenPartialHomeomorph W V3) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hrep : ∀ j, ∃ (A : Set E) (f : E → V3), FinitePiecewiseAffineOn f A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = f x)
    {O : Set X} (hO : IsOpen O)
    (hMF : ∀ x ∈ M.source ∩ O, (M x : E) = F x) :
    ∀ i j, ((e i).restrOpen O hO).symm.trans (M.trans (atlas j)) ∈
      piecewiseAffineGroupoid V3 := by
  intro i j
  let Q := (e i).restrOpen O hO
  let q := M.symm.trans Q
  have hq : LocallyPiecewiseAffineOn (fun z => (q.symm z : E)) q.target := by
    apply ((hF i).mono q.open_target (fun z hz => hz.1.1)).congr
    intro z hz
    exact (hMF ((e i).symm z) ⟨hz.2,hz.1.2⟩).symm
  obtain ⟨A,f,hf,hval⟩ := hrep j
  have ht := q.mem_piecewiseAffineGroupoid_transition_of_locallyPL_inverse (atlas j) hq hf
    (fun x hx => (hval x hx).1) (fun x hx => (hval x hx).2)
  simpa only [q,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc] using ht

theorem partial_pullback_chart_transition_mem
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (M : OpenPartialHomeomorph X Y) (a b : OpenPartialHomeomorph Y V3)
    (hab : a.symm.trans b ∈ piecewiseAffineGroupoid V3) :
    (M.trans a).symm.trans (M.trans b) ∈ piecewiseAffineGroupoid V3 := by
  let T := (M.trans a).symm.trans (M.trans b)
  apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
  have hsub : T.source ⊆ (a.symm.trans b).source := by
    intro z hz
    refine ⟨hz.1.1,?_⟩
    have h : M (M.symm (a.symm z)) ∈ b.source := hz.2.2
    rwa [M.right_inv hz.1.2] at h
  apply (hab.1.mono T.open_source hsub).congr
  intro z hz
  change b (a.symm z) = b (M (M.symm (a.symm z)))
  rw [M.right_inv hz.1.2]

theorem exists_global_partial_pullback_atlas
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (M : OpenPartialHomeomorph X W)
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X} (he : PLDomain e R)
    (atlas : κ → OpenPartialHomeomorph W V3) (ha : PLDomain atlas univ)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hrep : ∀ j, ∃ (A : Set E) (f : E → V3), FinitePiecewiseAffineOn f A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = f x)
    {O : Set X} (hO : IsOpen O) (hcover : M.source ∪ O = univ)
    (hfront : frontier R ⊆ O) (hMF : ∀ x ∈ M.source ∩ O, (M x : E) = F x) :
    ∃ a : (ι ⊕ κ) → OpenPartialHomeomorph X V3,
      (∀ i, a (Sum.inl i) = (e i).restrOpen O hO) ∧
      (∀ j, a (Sum.inr j) = M.trans (atlas j)) ∧ PLDomain a R ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) := by
  let old := fun i => (e i).restrOpen O hO
  let new := fun j => M.trans (atlas j)
  let a : (ι ⊕ κ) → OpenPartialHomeomorph X V3 := Sum.elim old new
  have hrestrict (c d : OpenPartialHomeomorph X V3)
      (h : c.symm.trans d ∈ piecewiseAffineGroupoid V3) :
      (c.restrOpen O hO).symm.trans (d.restrOpen O hO) ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact h.1.mono ((c.restrOpen O hO).symm.trans (d.restrOpen O hO)).open_source
      (fun _ hx => ⟨hx.1.1,hx.2.1⟩)
  have hcross := retained_partial_pullback_chart_transition M e atlas F hF hrep hO hMF
  have hcompat (i j : ι ⊕ κ) : (a i).symm.trans (a j) ∈ piecewiseAffineGroupoid V3 := by
    rcases i with i | i <;> rcases j with j | j
    · exact hrestrict _ _ (he.compatible i j)
    · exact hcross i j
    · change (M.trans (atlas i)).symm.trans ((e j).restrOpen O hO) ∈ _
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hcross j i)
    · change (M.trans (atlas i)).symm.trans (M.trans (atlas j)) ∈ _
      exact partial_pullback_chart_transition_mem M _ _ (ha.compatible i j)
  have hdomain : PLDomain a R := by
    refine ⟨?_,hcompat,he.closed,?_⟩
    · intro x
      have hx : x ∈ M.source ∪ O := hcover.symm ▸ mem_univ x
      rcases hx with hx | hx
      · obtain ⟨j,hj⟩ := ha.cover (M x)
        exact ⟨Sum.inr j,hx,hj⟩
      · obtain ⟨i,hi⟩ := he.cover x
        exact ⟨Sum.inl i,hi,hx⟩
    · intro x hx
      obtain ⟨ell,v,B,hv,hxB,hzero,hB,hhalf⟩ := he.halfspace x hx
      refine ⟨ell,v,B.restrOpen O hO,hv,⟨hxB,hfront hx⟩,hzero,?_,?_⟩
      · intro i
        apply pl_transition_mem_of_overlap_cover old
        · intro y hy
          obtain ⟨j,hj⟩ := he.cover y
          exact ⟨j,hj,hy.2.2⟩
        · intro j
          exact hcompat (Sum.inl j) i
        · intro j
          exact hrestrict _ _ (hB j)
      · intro y hy
        exact hhalf y hy.1
  obtain ⟨hforward,hreverse⟩ :=
    chartwisePLOn_identity_domain_both_of_restricted_transitions e a he hdomain hO
      (fun i j => hcompat (Sum.inl i) j)
  exact ⟨a,fun _ => rfl,fun _ => rfl,hdomain,hforward,hreverse⟩

theorem exists_global_open_pullback_atlas
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : Set X} [Nonempty V] (hV : IsOpen V) {W : Set E} (H : V ≃ₜ W)
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X} (he : PLDomain e R)
    (atlas : κ → OpenPartialHomeomorph W V3) (ha : PLDomain atlas univ)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hrep : ∀ j, ∃ (A : Set E) (f : E → V3), FinitePiecewiseAffineOn f A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = f x)
    {O : Set X} (hO : IsOpen O) (hcover : V ∪ O = univ)
    (hfront : frontier R ⊆ O) (hHF : ∀ x : V, (x : X) ∈ O → (H x : E) = F x) :
    let j := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → X)
    let M := j.symm.transHomeomorph H
    ∃ a : (ι ⊕ κ) → OpenPartialHomeomorph X V3,
      (∀ i, a (Sum.inl i) = (e i).restrOpen O hO) ∧
      (∀ k, a (Sum.inr k) = M.trans (atlas k)) ∧ PLDomain a R ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) := by
  let j := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → X)
  let M := j.symm.transHomeomorph H
  have hMs : M.source = V := by
    change (Subtype.val : V → X) '' univ = V
    simp only [image_univ,Subtype.range_coe]
  apply exists_global_partial_pullback_atlas M e he atlas ha F hF hrep hO
    (hMs.symm ▸ hcover) hfront
  intro x hx
  have hxj : x ∈ j.target := hx.1
  have hval : (j.symm x : X) = x := j.right_inv hxj
  change (H (j.symm x) : E) = F x
  exact (hHF (j.symm x) (hval.symm ▸ hx.2)).trans (congrArg F hval)

end PoincareConjecture.M76
