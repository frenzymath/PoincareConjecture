import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem capRimSet_subset_closure_outside_strip
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U) (b : Bool) :
    P.capRimSet b ⊆ closure (F \ P.closedStrip) := by
  rintro x ⟨⟨u, s⟩, ⟨hu, hs⟩, rfl⟩
  have hs' : s = if b then (1 / 2 : ℝ) else -(1 / 2) := hs
  subst s
  let height : ℝ → ℝ := fun t => if b then 1 / 2 + t / 4 else -(1 / 2 + t / 4)
  let coords : ℝ → V2 × ℝ := fun t => (u, height t)
  have hc : Continuous coords := by
    dsimp [coords, height]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hfull : MapsTo coords (Icc (0 : ℝ) 1) (D ×ˢ Icc (-1 : ℝ) 1) := by
    intro t ht
    refine ⟨sphere_subset_closedBall hu, ?_⟩
    cases b <;> simp only [coords, height, Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [ht.1, ht.2]
  have hp : ContinuousOn (P.map ∘ coords) (Icc (0 : ℝ) 1) :=
    P.polyhedral.continuousOn.comp hc.continuousOn hfull
  have hmaps : MapsTo (P.map ∘ coords) (Ioc (0 : ℝ) 1) (F \ P.closedStrip) := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    refine ⟨(P.protected_frontier_iff hcut hsmall _ (hfull htcc)).mpr hu, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwfull : w ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
    have hh := congrArg Prod.snd (P.injective hwfull (hfull htcc) heq)
    change w.2 = height t at hh
    cases b <;> simp only [height, Bool.false_eq_true, ↓reduceIte] at hh <;>
      linarith [hw.2.1, hw.2.2, ht.1]
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  have hm := ((hp 0 (by norm_num)).mono Ioc_subset_Icc_self).mem_closure hzero hmaps
  simpa [Function.comp_def, coords, height] using hm

theorem retained_frontier_eq_closure_outside_strip
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))))) :
    F \ P.openStrip = closure (F \ P.closedStrip) := by
  have hpre : IsOpen ((Subtype.val : F → X) ⁻¹' P.openStrip) := by
    have heq : (Subtype.val : F → X) ⁻¹' P.openStrip =
        (Subtype.val : F → X) ⁻¹' (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
      ext x
      constructor
      · rintro ⟨z, hz, heq⟩
        have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
          ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
        exact ⟨z, ⟨(P.protected_frontier_iff hcut hsmall z hzfull).mp
          (heq.symm ▸ x.property), hz.2⟩, heq⟩
      · rintro ⟨z, hz, heq⟩
        exact ⟨z, ⟨sphere_subset_closedBall hz.1, hz.2⟩, heq⟩
    rw [heq]
    exact isOpen_protected_frontier_preimage hcut hlateral
  have hclosed : IsClosed (F \ P.openStrip) := by
    have h := hF.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hpre.isClosed_compl
    have heq : (Subtype.val : F → X) '' ((Subtype.val : F → X) ⁻¹' P.openStrip)ᶜ =
        F \ P.openStrip := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hx, hn⟩
        exact ⟨⟨x, hx⟩, hn, rfl⟩
    exact heq ▸ h
  apply Subset.antisymm
  · intro x hx
    by_cases hb : x ∈ P.closedStrip
    · rcases hb with ⟨z, hz, rfl⟩
      have hzfull : z ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      have hq := (P.protected_frontier_iff hcut hsmall z hzfull).mp hx.1
      have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
        by_contra hn
        push Not at hn
        exact hx.2 ⟨z, ⟨hz.1, lt_of_le_of_ne hz.2.1 hn.1.symm,
          lt_of_le_of_ne hz.2.2 hn.2⟩, rfl⟩
      rcases ht with ht | ht
      · exact P.capRimSet_subset_closure_outside_strip hcut hsmall false
          ⟨z, ⟨hq, ht⟩, rfl⟩
      · exact P.capRimSet_subset_closure_outside_strip hcut hsmall true
          ⟨z, ⟨hq, ht⟩, rfl⟩
    · exact subset_closure ⟨hx.1, hb⟩
  · apply closure_minimal _ hclosed
    intro x hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact hx.2 ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩

theorem closure_graph_outside_strip
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace E] [T2Space E]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (phi : X → E) (hphi : Continuous phi) :
    closure (phi '' (F \ P.closedStrip)) = phi '' (F \ P.openStrip) := by
  have heq := P.retained_frontier_eq_closure_outside_strip hF hcut hsmall hlateral
  have hcl : closure (F \ P.closedStrip) ⊆ F :=
    closure_minimal sdiff_subset hF.isClosed
  have hc : IsCompact (closure (F \ P.closedStrip)) :=
    hF.of_isClosed_subset isClosed_closure hcl
  rw [heq]
  exact Subset.antisymm
    (closure_minimal (image_mono subset_closure) (hc.image hphi).isClosed)
    (image_closure_subset_closure_image hphi)

theorem closure_graph_frontier_sdiff_annulus
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace E] [T2Space E]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (phi : X → E) (hphi : Continuous phi) (hinj : InjOn phi F) :
    closure (phi '' F \ phi '' (F ∩ P.closedStrip)) = phi '' (F \ P.openStrip) := by
  rw [← hinj.image_sdiff]
  exact P.closure_graph_outside_strip hF hcut hsmall hlateral phi hphi

end PoincareConjecture.M76.OriginalDiskProduct
