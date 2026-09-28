import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCappedProperArc
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneConeExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_conical_boundary_pair_chart
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {C p n q w : Set E} {D P N Q W : Set F} {a b : E} {A B : F}
    (hC : IsCompact C) (hD : IsCompact D)
    (hcvC : Convex ℝ C) (hcvD : Convex ℝ D)
    (hC0 : (0 : E) ∈ interior C) (hD0 : (0 : F) ∈ interior D)
    (hp : IsFinitePLBallPair (ℝ × ℝ) p q)
    (hn : IsFinitePLBallPair (ℝ × ℝ) n q)
    (hP : IsFinitePLBallPair (ℝ × ℝ) P Q)
    (hN : IsFinitePLBallPair (ℝ × ℝ) N Q)
    (hc : p ∪ n = frontier C) (hpc : p ∩ n = q)
    (hd : P ∪ N = frontier D) (hPD : P ∩ N = Q)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {A, B})
    (hab : a ≠ b) (hAB : A ≠ B)
    (ha : a ∈ q) (hb : b ∈ q) (hA : A ∈ Q) (hB : B ∈ Q)
    (hproper : w \ {a, b} ⊆ p \ q)
    (hProper : W \ {A, B} ⊆ P \ Q) :
    ∃ H : OpenPartialHomeomorph E F,
      H.source = interior C ∧ H.target = interior D ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H 0 = 0 ∧
      (∀ x ∈ H.source, x ∈ convexJoin ℝ {0} p ↔ H x ∈ convexJoin ℝ {0} P) ∧
      ∀ x ∈ H.source, x ∈ convexJoin ℝ {0} w ↔ H x ∈ convexJoin ℝ {0} W := by
  obtain ⟨e, he, hep, _, hew⟩ := exists_finitePL_capped_proper_arc_map
    hp hn hP hN hc hpc hd hPD hw hW hab hAB ha hb hA hB hproper hProper
  obtain ⟨g, G, hG, hGg, hg0, hrad⟩ :=
    exists_radial_convex_extension he hC hD hcvC hcvD hC0 hD0
  obtain ⟨H, hHs, hHt, hHPL, hiHPL, _, _, hHG, _⟩ :=
    hG.exists_interior_chart hdim
  have hHg (x : E) (hx : x ∈ C) : H x = g x :=
    (hHG ⟨x, hx⟩).trans (hGg ⟨x, hx⟩)
  have hcone (s : Set E) (t : Set F)
      (hs : s ⊆ frontier C) (ht : t ⊆ frontier D)
      (hmem : ∀ x : frontier C, (x : E) ∈ s ↔ (e x : F) ∈ t)
      (x : E) (hx : x ∈ H.source) :
      x ∈ convexJoin ℝ {0} s ↔ H x ∈ convexJoin ℝ {0} t := by
    have heimage : (fun z : frontier C => (e z : F)) ''
        ((Subtype.val : frontier C → E) ⁻¹' s) = t := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hmem z).mp hz
      · intro hy
        refine ⟨e.symm ⟨y, ht hy⟩, ?_, ?_⟩
        · exact (hmem _).mpr (by simpa only [e.apply_symm_apply] using hy)
        · exact congrArg Subtype.val (e.apply_symm_apply ⟨y, ht hy⟩)
    have himage : g '' convexJoin ℝ {0} s = convexJoin ℝ {0} t := by
      rw [radial_extension_image_convexJoin e g hrad hs, heimage]
    have hsC : convexJoin ℝ {(0 : E)} s ⊆ C :=
      convexJoin_subset (singleton_subset_iff.mpr (interior_subset hC0))
        (hs.trans hC.isClosed.frontier_subset) hcvC
    have hxC : x ∈ C := interior_subset (hHs ▸ hx)
    rw [hHg x hxC, ← himage]
    constructor
    · exact fun hx' => mem_image_of_mem g hx'
    · rintro ⟨y, hy, hyx⟩
      have hxy : G ⟨y, hsC hy⟩ = G ⟨x, hxC⟩ := by
        apply Subtype.ext
        simpa only [hGg] using hyx
      have hyxeq : y = x := congrArg Subtype.val (G.injective hxy)
      exact hyxeq ▸ hy
  have hpC : p ⊆ frontier C := subset_union_left.trans hc.subset
  have hPD' : P ⊆ frontier D := subset_union_left.trans hd.subset
  have hwC : w ⊆ frontier C := by
    intro x hx
    apply hpC
    by_cases hm : x ∈ ({a, b} : Set E)
    · exact hp.1 (hm.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb))
    · exact (hproper ⟨hx, hm⟩).1
  have hWD : W ⊆ frontier D := by
    intro x hx
    apply hPD'
    by_cases hm : x ∈ ({A, B} : Set F)
    · exact hP.1 (hm.elim (fun h => h.symm ▸ hA) (fun h => h.symm ▸ hB))
    · exact (hProper ⟨hx, hm⟩).1
  exact ⟨H, hHs, hHt, hHPL, hiHPL,
    (hHg 0 (interior_subset hC0)).trans hg0,
    hcone p P hpC hPD' hep, hcone w W hwC hWD hew⟩

end PoincareConjecture.M76.HamiltonIndexOne
