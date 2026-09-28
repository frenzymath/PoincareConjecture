import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLEqualityLoci
import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_finite_local_halfspace_traces
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite) {R : Set V3}
    (hcharts : ∀ x ∈ K.space, ∃ Q : OpenPartialHomeomorph V3 V3,
      x ∈ Q.source ∧ LocallyPiecewiseAffineOn Q Q.source ∧
      (Q.source ⊆ interior R ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ), ell.toAffineMap.linear ≠ 0 ∧
          ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y))) :
    ∃ P B : SimplicialComplex ℝ V3, P.faces.Finite ∧ B.faces.Finite ∧
      P.space = K.space ∩ R ∧ B.space = K.space ∩ frontier R := by
  classical
  have hlocal (x : K.space) :
      ∃ (N P B : SimplicialComplex ℝ V3) (W : Set K.space),
        N.space ⊆ K.space ∧ IsOpen W ∧ x ∈ W ∧ Subtype.val '' W ⊆ N.space ∧
        P.faces.Finite ∧ B.faces.Finite ∧
        P.space = N.space ∩ R ∧ B.space = N.space ∩ frontier R := by
    obtain ⟨Q, hxQ, hQ, hkind⟩ := hcharts x x.property
    obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNQ⟩ :=
      K.exists_relative_polyhedral_neighborhood hK x
        (Q.open_source.preimage continuous_subtype_val) hxQ
    have hNsource : N.space ⊆ Q.source := by
      intro y hy
      exact hNQ (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
    have hcoords : FinitePiecewiseAffineOn Q N.space :=
      hQ.comp_finitePiecewiseAffineOn
        ((N.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hN)
        hNsource
    have hbot : (⊥ : SimplicialComplex ℝ V3).faces.Finite := by
      rw [SimplicialComplex.faces_bot]
      exact finite_empty
    rcases hkind with hin | ⟨ell, hlin, hhalf⟩
    · refine ⟨N, N, ⊥, W, hNK, hW, hxW, hWN, hN, hbot, ?_, ?_⟩
      · exact (inter_eq_left.mpr (fun y hy => interior_subset (hin (hNsource hy)))).symm
      · rw [SimplicialComplex.space_bot]
        exact (eq_empty_iff_forall_notMem.mpr (fun y hy =>
          disjoint_left.mp disjoint_interior_frontier (hin (hNsource hy.1)) hy.2)).symm
    · let a : V3 →ᵃ[ℝ] ℝ := ell.toAffineMap
      obtain ⟨P, hP, hPs⟩ := hcoords.exists_finite_halfspace_preimage {-a}
      obtain ⟨B, hB, hBs⟩ := hcoords.exists_finite_halfspace_preimage {a, -a}
      have hfront := Q.isImage_frontier_of_affine_nonneg ell hlin hhalf
      refine ⟨N, P, B, W, hNK, hW, hxW, hWN, hP, hB, ?_, ?_⟩
      · rw [hPs]
        ext y
        simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_singleton, forall_eq]
        change (y ∈ N.space ∧ -ell (Q y) ≤ 0) ↔ (y ∈ N.space ∧ y ∈ R)
        exact and_congr_right fun hy => by rw [neg_nonpos, hhalf _ (hNsource hy)]
      · rw [hBs]
        ext y
        simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
          forall_eq_or_imp, forall_eq]
        change (y ∈ N.space ∧ ell (Q y) ≤ 0 ∧ -ell (Q y) ≤ 0) ↔
          (y ∈ N.space ∧ y ∈ frontier R)
        apply and_congr_right
        intro hy
        rw [neg_nonpos, ← hfront.apply_mem_iff (hNsource hy)]
        exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  choose N P B W hNK hW hxW hWN hP hB hPs hBs using hlocal
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  obtain ⟨P0, hP0, hP0s, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun x : t => P x) (fun x => hP x)
  obtain ⟨B0, hB0, hB0s, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun x : t => B x) (fun x => hB x)
  have hunion (L : K.space → SimplicialComplex ℝ V3) (Z : Set V3)
      (hL : ∀ x, (L x).space = (N x).space ∩ Z) :
      (⋃ x : t, (L x).space) = K.space ∩ Z := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp hy
      rw [hL x] at hx
      exact ⟨hNK x hx.1, hx.2⟩
    · intro hy
      obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨y, hy.1⟩ : K.space)))
      refine mem_iUnion.mpr ⟨⟨x, hxt⟩, ?_⟩
      rw [hL x]
      exact ⟨hWN x (mem_image_of_mem Subtype.val hx), hy.2⟩
  exact ⟨P0, B0, hP0, hB0, hP0s.trans (hunion P R hPs),
    hB0s.trans (hunion B (frontier R) hBs)⟩

end PoincareConjecture.M76
