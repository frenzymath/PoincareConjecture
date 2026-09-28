import PoincareConjecture.Proofs.M76.Mathlib.HamiltonOverlapCorrection
import Mathlib.Topology.OpenPartialHomeomorph.Constructions










set_option autoImplicit false

open Set Topology Geometry

universe u v w

namespace PoincareConjecture.M76




theorem nonempty_supportedPLOverlapCorrection_of_covered
    {M : Type u} {E : Type v} {ι : Type w}
    [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (c : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E)
    (d : OpenPartialHomeomorph M E) (Q : Set M) (hQ : IsCompact Q)
    (hQO : Q ⊆ (⋃ i, (c i).source) ∩ d.source)
    (hcovered : ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
      [LocallyCompactSpace X] (a : ι → OpenPartialHomeomorph X E),
      (∀ i j, (a i).symm.trans (a j) ∈ piecewiseAffineGroupoid E) →
      (⋃ i, (a i).source) = univ →
      ∀ (b : OpenPartialHomeomorph X E), b.source = univ →
      ∀ K : Set X, IsCompact K →
      ∃ (G : X ≃ₜ X) (U S : Set X), IsOpen U ∧ IsCompact S ∧
        EqOn G id Sᶜ ∧ K ⊆ U ∧
        ∀ i, LocallyPiecewiseAffineOn ((b ∘ G) ∘ (a i).symm)
          ((a i).target ∩ (a i).symm ⁻¹' U)) :
    Nonempty (OpenPartialHomeomorph.SupportedPLOverlapCorrection c d Q) := by
  classical
  let O : TopologicalSpace.Opens M :=
    ⟨(⋃ i, (c i).source) ∩ d.source,
      (isOpen_iUnion fun i => (c i).open_source).inter d.open_source⟩
  by_cases hO : Nonempty O
  · let a : ι → OpenPartialHomeomorph O E := fun i => (c i).subtypeRestr hO
    let b : OpenPartialHomeomorph O E := d.subtypeRestr hO
    have hb : b.source = univ := by
      ext x
      simp only [b, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage,
        mem_univ, iff_true]
      exact x.property.2
    let : T2Space O := (b.isOpenEmbedding hb).isEmbedding.t2Space
    let : LocallyCompactSpace O := (b.isOpenEmbedding hb).locallyCompactSpace
    have hac : ∀ i j, (a i).symm.trans (a j) ∈ piecewiseAffineGroupoid E := by
      intro i j
      apply (piecewiseAffineGroupoid E).mem_of_eqOnSource
        (closedUnderRestriction' (hcompat i j)
          ((c i).isOpen_inter_preimage_symm O.isOpen))
      exact OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr hO (c i) (c j)
    have ha : (⋃ i, (a i).source) = univ := by
      apply eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := mem_iUnion.mp x.property.1
      exact mem_iUnion.mpr ⟨i, by
        simpa only [a, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hi⟩
    let Q0 : Set O := ((↑) : O → M) ⁻¹' Q
    have hQ0 : IsCompact Q0 :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hQ
        (fun x hx => ⟨⟨x, hQO hx⟩, rfl⟩)
    obtain ⟨G, U, S, hU, hS, hfix, hQU, hpl⟩ := hcovered O a hac ha b hb Q0 hQ0
    let N : Set M := ((↑) : O → M) '' U
    let T : Set M := ((↑) : O → M) '' S
    let coordinates : M → E := fun x =>
      if hx : x ∈ (O : Set M) then d (G ⟨x, hx⟩) else d x
    have hN : IsOpen N := O.isOpen.isOpenMap_subtype_val U hU
    refine ⟨{
      neighborhood := N
      neighborhood_open := hN
      core_subset := ?_
      neighborhood_subset := ?_
      support := T
      support_compact := hS.image continuous_subtype_val
      support_subset := ?_
      correction := G
      fixed := ?_
      coordinates := coordinates
      coordinates_eq := ?_
      locallyPL := ?_ }⟩
    · intro x hx
      exact ⟨⟨x, hQO hx⟩, hQU hx, rfl⟩
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · rintro _ ⟨x, _, rfl⟩
      exact x.property
    · intro x hx
      exact hfix (fun hxs => hx ⟨x, hxs, rfl⟩)
    · intro x
      have hxO : (x : M) ∈ (O : Set M) := x.property
      dsimp only [coordinates]
      rw [dif_pos hxO]
      exact congrArg (fun z : O => d (G z)) (Subtype.ext rfl)
    · intro i
      have htarget : (c i).target ∩ (c i).symm ⁻¹' N =
          (a i).target ∩ (a i).symm ⁻¹' U := by
        ext y
        constructor
        · rintro ⟨hy, x, hxU, hxy⟩
          have hyO : (c i).symm y ∈ (O : Set M) := hxy ▸ x.property
          have hya : y ∈ (a i).target := by
            refine ⟨hy, ?_⟩
            change (c i).symm y ∈ (O.openPartialHomeomorphSubtypeCoe hO).target
            rwa [O.openPartialHomeomorphSubtypeCoe_target]
          refine ⟨hya, ?_⟩
          have heq : (a i).symm y = x :=
            Subtype.ext (((c i).subtypeRestr_symm_apply hO hya).trans hxy.symm)
          simpa only [mem_preimage, heq] using hxU
        · intro hy
          refine ⟨(c i).subtypeRestr_target_subset hO hy.1, ?_⟩
          exact ⟨(a i).symm y, hy.2, (c i).subtypeRestr_symm_apply hO hy.1⟩
      have hpli := hpl i
      rw [← htarget] at hpli
      apply hpli.congr
      intro y hy
      have hya : y ∈ (a i).target := (htarget.subset hy).1
      have hval : ((a i).symm y : M) = (c i).symm y :=
        (c i).subtypeRestr_symm_apply hO hya
      have hyO : (c i).symm y ∈ (O : Set M) := hval ▸ ((a i).symm y).property
      change d (G ((a i).symm y)) = coordinates ((c i).symm y)
      rw [show coordinates ((c i).symm y) = d (G ⟨(c i).symm y, hyO⟩) by
        simp only [coordinates, dif_pos hyO]]
      exact congrArg (fun x : O => d (G x)) (Subtype.ext hval)
  · refine ⟨{
      neighborhood := ∅
      neighborhood_open := isOpen_empty
      core_subset := ?_
      neighborhood_subset := empty_subset _
      support := ∅
      support_compact := isCompact_empty
      support_subset := empty_subset _
      correction := Homeomorph.refl _
      fixed := fun _ _ => rfl
      coordinates := d
      coordinates_eq := fun _ => rfl
      locallyPL := ?_ }⟩
    · intro x hx
      exact False.elim (hO ⟨⟨x, hQO hx⟩⟩)
    · intro i x hx
      exact False.elim hx.2

end PoincareConjecture.M76
