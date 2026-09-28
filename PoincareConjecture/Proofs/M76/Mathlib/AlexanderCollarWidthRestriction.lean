import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineSlabComplex
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMinimum

set_option autoImplicit false

open Set

namespace Geometry.AlexanderCollarSlab

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}

theorem exists_finite_slab_complex (M : AlexanderCollarSlab S A q β) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧
      K.space = S ∩ {x | A x ∈ Icc 0 β} := by
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := M.chart_finitePL.symm
  obtain ⟨K, hK, hKs⟩ := J.exists_finite_triangulation_union
    M.residualComplex hJ M.residual_finite
  exact ⟨K, hK, hKs.trans (by rw [hJs, M.residual_space, M.cover])⟩

theorem exists_width_restriction (M : AlexanderCollarSlab S A q β)
    {γ : ℝ} (hγ : 0 < γ) (hγβ : γ ≤ β) :
    ∃ N : AlexanderCollarSlab S A q γ,
      N.upper = (fun x => min (M.upper x) γ) ∧
      N.collar = M.collar ∩ {x | A x ∈ Icc 0 γ} ∧
      N.residual = (M.residual ∩ {x | A x ∈ Icc 0 γ}) ∪
        (S ∩ {x | A x = γ}) := by
  let B : Set (E × ℝ) := {p | p.1 ∈ S ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (min (M.upper p.1) γ)}
  let T : Set E := M.collar ∩ {x | A x ∈ Icc 0 γ}
  let R : Set E := (M.residual ∩ {x | A x ∈ Icc 0 γ}) ∪
    (S ∩ {x | A x = γ})
  have hB : B ⊆ {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans (min_le_left _ _)⟩
  have hT : T ⊆ M.collar := inter_subset_left
  have htest (p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) :
      (p : E × ℝ) ∈ B ↔ (M.chart p : E) ∈ T := by
    constructor
    · intro hp
      refine ⟨(M.chart p).property, ?_⟩
      change A (M.chart p) ∈ Icc 0 γ
      rw [M.height p]
      exact ⟨hp.2.1, hp.2.2.trans (min_le_right _ _)⟩
    · intro hp
      refine ⟨p.property.1, p.property.2.1, le_min p.property.2.2 ?_⟩
      have h := hp.2.2
      rwa [M.height p] at h
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := M.chart_finitePL.symm
  obtain ⟨JT, hJT, hJTs⟩ := J.exists_finite_affineSlab_complex hJ A 0 γ
  have hJTT : JT.space = T := by rw [hJTs, hJs]
  let C := M.chart.restrictSubsets hB hT htest
  have hC : C.IsFinitePL := M.chart_finitePL.restrictSubsets_of_target
    hB hT htest JT hJT hJTT
  obtain ⟨K, hK, hKs⟩ := M.exists_finite_slab_complex
  obtain ⟨U, hU, hUs⟩ := K.exists_finite_affineLevel_complex hK A γ
  have htop : U.space = S ∩ {x | A x = γ} := by
    rw [hUs, hKs]
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · intro hx
      refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      change A x ∈ Icc 0 β
      rw [hx.2]
      exact ⟨hγ.le, hγβ⟩
  obtain ⟨V, hV, hVs⟩ := M.residualComplex.exists_finite_affineSlab_complex
    M.residual_finite A 0 γ
  obtain ⟨W, hW, hWs⟩ := V.exists_finite_triangulation_union U hV hU
  have hWR : W.space = R := by rw [hWs, hVs, M.residual_space, htop]
  have hconst : FinitePiecewiseAffineOn (fun _ : E => γ) (S ∩ {x | A x = 0}) := by
    obtain ⟨L, hL, hLs, _⟩ := M.upper_finitePL
    exact ⟨L, hL, hLs, L.affineOnFaces_affine (ContinuousAffineMap.const ℝ E γ)⟩
  have hupper : FinitePiecewiseAffineOn (fun x => min (M.upper x) γ)
      (S ∩ {x | A x = 0}) := M.upper_finitePL.min hconst
  have hcollarS : M.collar ⊆ S :=
    subset_union_left.trans (M.cover.subset.trans inter_subset_left)
  have hresidualS : M.residual ⊆ S :=
    subset_union_right.trans (M.cover.subset.trans inter_subset_left)
  let N : AlexanderCollarSlab S A q γ := {
    width_pos := hγ
    apex_mem := M.apex_mem
    apex_height := M.apex_height
    upper := fun x => min (M.upper x) γ
    collar := T
    residual := R
    residualComplex := W
    chart := C
    chart_finitePL := hC
    residual_finite := hW
    residual_space := hWR
    cover := by
      ext x
      constructor
      · rintro (hx | hx | hx)
        · exact ⟨hcollarS hx.1, hx.2⟩
        · exact ⟨hresidualS hx.1, hx.2⟩
        · refine ⟨hx.1, ?_⟩
          change A x ∈ Icc 0 γ
          rw [hx.2]
          exact ⟨hγ.le, le_rfl⟩
      · intro hx
        have hxold : x ∈ M.collar ∪ M.residual :=
          M.cover.symm.subset ⟨hx.1, hx.2.1, hx.2.2.trans hγβ⟩
        rcases hxold with hc | hr
        · exact Or.inl ⟨hc, hx.2⟩
        · exact Or.inr (Or.inl ⟨hr, hx.2⟩)
    residual_zero := by
      intro x hx
      rcases hx.1 with hr | ht
      · exact M.residual_zero ⟨hr.1, hx.2⟩
      · exact (ne_of_gt hγ (ht.2.symm.trans hx.2)).elim
    roof_contact := by
      intro p
      let pold := (⟨p, hB p.property⟩ :
        {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)})
      have hval : (C p : E) = M.chart pold := rfl
      have hheight : A (C p) = (p : E × ℝ).2 := M.height pold
      have hbound : (p : E × ℝ).2 ≤ min (M.upper (p : E × ℝ).1) γ :=
        p.property.2.2
      constructor
      · intro hp
        apply le_antisymm hbound
        rcases hp with hr | ht
        · have hu : (p : E × ℝ).2 = M.upper (p : E × ℝ).1 :=
            (M.roof_contact pold).mp (hval ▸ hr.1)
          exact (min_le_left _ _).trans hu.symm.le
        · have ht' : (p : E × ℝ).2 = γ := hheight.symm.trans ht.2
          exact (min_le_right _ _).trans ht'.symm.le
      · intro hp
        by_cases hu : M.upper (p : E × ℝ).1 ≤ γ
        · have hp' : (p : E × ℝ).2 = M.upper (p : E × ℝ).1 :=
            hp.trans (min_eq_left hu)
          exact Or.inl ⟨hval.symm ▸ (M.roof_contact pold).mpr hp', (C p).property.2⟩
        · have hp' : (p : E × ℝ).2 = γ := hp.trans (min_eq_right (le_of_not_ge hu))
          exact Or.inr ⟨hcollarS (C p).property.1, hheight.trans hp'⟩
    upper_finitePL := hupper
    upper_bounds := fun x hx =>
      ⟨le_min (M.upper_bounds x hx).1 hγ.le, min_le_right _ _⟩
    apex_upper := by rw [M.apex_upper, min_eq_left hγ.le]
    upper_pos := fun x hx hne => lt_min (M.upper_pos x hx hne) hγ
    height := fun p => M.height ⟨p, hB p.property⟩
    bottom := fun p => M.bottom ⟨p, hB p.property⟩
    bottom_covered := by
      intro x hx
      refine ⟨M.bottom_covered hx, ?_⟩
      change A x ∈ Icc 0 γ
      rw [hx.2]
      exact ⟨le_rfl, hγ.le⟩ }
  exact ⟨N, rfl, rfl, rfl⟩

end Geometry.AlexanderCollarSlab
