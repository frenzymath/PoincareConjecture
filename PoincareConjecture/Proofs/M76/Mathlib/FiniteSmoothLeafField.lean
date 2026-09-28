import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFaceLeafAttachment
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFrontierAttachment
import Mathlib.Data.Finset.Max










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

open EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem exists_smoothLeafField_near_faces (K : SimplicialComplex ℝ E) (m : ℕ)
    (hfull : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = m + 1)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (hpositive : ∀ s ∈ K.faces, 2 ≤ s.card →
      ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (S : Finset (Finset E)) (hSK : ∀ s ∈ S, s ∈ K.faces)
    (hdown : ∀ s ∈ S, ∀ t ∈ K.faces, t ⊆ s → t ∈ S) :
    ∃ U : Set E, IsOpen U ∧ (⋃ s ∈ S, convexHull ℝ (s : Set E)) ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E) ∧
        ∀ s ∈ S, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  classical
  revert hSK hdown
  induction S using Finset.induction_on_max_value (fun t : Finset E => t.card) with
  | empty =>
      intro _ _
      refine ⟨∅, isOpen_empty, by simp, fun _ => ⟨⊥⟩,
        IsSmoothLeafFieldOn.const ⟨⊥⟩ ∅, ?_, ?_⟩ <;> simp
  | insert s S hsnot hmax ih =>
      intro hSK hdown
      have hsK : s ∈ K.faces := hSK s (Finset.mem_insert_self s S)
      have hSK' : ∀ t ∈ S, t ∈ K.faces := fun t ht => hSK t (Finset.mem_insert_of_mem ht)
      have hdown' : ∀ t ∈ S, ∀ r ∈ K.faces, r ⊆ t → r ∈ S := by
        intro t ht r hr hrt
        rcases Finset.mem_insert.mp (hdown t (Finset.mem_insert_of_mem ht) r hr hrt) with he | hrS
        · subst r
          have hts : t = s := (Finset.eq_of_subset_of_card_le hrt (hmax t ht)).symm
          exact False.elim (hsnot (hts ▸ ht))
        · exact hrS
      obtain ⟨U, hU, hBU, P, hP, hdim, hPT⟩ := ih hSK' hdown'
      let B := ⋃ t ∈ S, convexHull ℝ (t : Set E)
      have hB : IsClosed B :=
        (S.finite_toSet.isCompact_biUnion
          (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
      have hproper : ∀ t ∈ K.faces, t ⊂ s → t ∈ S := by
        intro t ht hts
        exact Finset.mem_of_mem_insert_of_ne
          (hdown s (Finset.mem_insert_self s S) t ht hts.subset) hts.ne
      have hboundary : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆ U := by
        intro x hx
        obtain ⟨t, ht, hts, hxt⟩ := K.exists_properFace_of_mem_intrinsicFrontier hsK hx
        exact hBU (mem_iUnion₂.mpr ⟨t, hproper t ht hts, hxt⟩)
      have hBS : B ∩ convexHull ℝ (s : Set E) ⊆
          intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
        rintro x ⟨hxB, hxs⟩
        obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxB
        exact K.inter_subset_intrinsicFrontier_of_card_le hsK (hSK' t ht)
          (fun he => hsnot (he ▸ ht)) (hmax t ht) ⟨hxt, hxs⟩
      have hstep : ∃ W : Set E, IsOpen W ∧ B ∪ convexHull ℝ (s : Set E) ⊆ W ∧
          ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
            (∀ x ∈ W, Module.finrank ℝ (R x).subspace + m = Module.finrank ℝ E) ∧
            R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ convexHull ℝ (s : Set E),
              (R x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
        by_cases hpos : 2 ≤ s.card
        · let := hpositive s hsK hpos
          obtain ⟨t, ht, hst, hcard⟩ := hfull s hsK
          apply hP.exists_simplicialFaceAttachment hU hB hBU K hsK ht hst m hcard
            hboundary hBS hdim
          intro x hx
          obtain ⟨r, hr, hrs, hxr⟩ := K.exists_properFace_of_mem_intrinsicFrontier hsK hx
          apply (hPT r (hproper r hr hrs) x hxr).mono
          intro y hy
          obtain ⟨q, hq, hyq⟩ := mem_space_iff.mp hy
          exact mem_space_iff.mpr ⟨q, K.closedFaceStar_antitone hrs.subset hq, hyq⟩
        · have hcard : s.card = 1 := by
            have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hsK)
            omega
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
          obtain ⟨Q⟩ := hvertices {v} hsK (by simp)
          have hinter : B ∩ {v} = ∅ := by
            apply subset_empty_iff.mp
            simpa only [Finset.coe_singleton, convexHull_singleton,
              intrinsicFrontier_singleton] using hBS
          have hPQ : P =ᶠ[𝓝ˢ (B ∩ {v})] (fun _ => Q.val) := by
            rw [hinter, nhdsSet_empty]
            exact Filter.eventually_bot
          obtain ⟨W, hW, hBW, R, hR, hsource, hRP, hRQ⟩ :=
            hP.exists_gluing (IsSmoothLeafFieldOn.const Q.val univ) hU isOpen_univ
              hB isClosed_singleton hBU (subset_univ _) hPQ
          simp only [Finset.coe_singleton, convexHull_singleton]
          refine ⟨W, hW, hBW, R, hR, ?_, hRP, ?_⟩
          · intro x hx
            rcases hsource x hx with ⟨hxU, hRx⟩ | ⟨_, hRx⟩
            · rw [hRx]
              exact hdim x hxU
            · rw [hRx]
              exact Q.property.1
          · intro x hx
            have hxv : x = v := hx
            subst x
            rw [hRQ.self_of_nhdsSet (mem_singleton v)]
            exact Q.property.2
      obtain ⟨W, hW, hcover, R, hR, hRdim, hRP, hRT⟩ := hstep
      refine ⟨W, hW, ?_, R, hR, hRdim, ?_⟩
      · intro x hx
        obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hcover (Or.inr hxt)
        · exact hcover (Or.inl (mem_iUnion₂.mpr ⟨t, ht, hxt⟩))
      · intro t ht x hx
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hRT x hx
        · rw [hRP.self_of_nhdsSet (show x ∈ B from mem_iUnion₂.mpr ⟨t, ht, hx⟩)]
          exact hPT t ht x hx





theorem exists_smoothLeafField_near_space (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (m : ℕ)
    (hfull : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = m + 1)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (hpositive : ∀ s ∈ K.faces, 2 ≤ s.card →
      ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space)) :
    ∃ U : Set E, IsOpen U ∧ K.space ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E) ∧
        ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  classical
  have h := K.exists_smoothLeafField_near_faces m hfull hvertices hpositive hfinite.toFinset
    (by simp) (by intro _ _ _ ht _; exact hfinite.mem_toFinset.mpr ht)
  simpa only [Set.Finite.mem_toFinset, space] using h

end Geometry.SimplicialComplex
