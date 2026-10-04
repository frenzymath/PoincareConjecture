import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.RicciFlow.Curvature.Energy.Regularity

/-!
# Order facts for the full curvature supremum

The annular evolution contract distinguishes the full curvature supremum from
the unit-input constant supplied by M63.  These small lemmas keep the
nonnegativity and pointwise upper-bound steps guarded by the required
boundedness hypothesis; in particular, they do not use an empty `sSup` as a
geometric witness.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Compactness bounds the range of the actual full curvature norm at every allowed flow
time. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CurvatureRange_bddAbove_of_compact
    (hcompact : IsCompact (Set.univ : Set M))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    BddAbove
      (Set.range (fun x : M => (F.connection t).curvatureTensorNorm x)) := by
  have hjoint : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).curvatureTensorNorm p.2)
      (Set.Icc a b ×ˢ Set.univ) := by
    have h := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).continuousOn.sqrt
    apply h.congr
    intro p _hp
    dsimp only
    rw [LeviCivitaData.curvatureDerivativeNorm_zero]
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  have hslice : ContinuousOn
      (fun x : M => (F.connection t).curvatureTensorNorm x) (Set.univ : Set M) := by
    have hmap : MapsTo (fun x : M => (t, x)) (Set.univ : Set M)
        (Set.Icc a b ×ˢ Set.univ) := by
      intro x _
      exact ⟨ht, mem_univ x⟩
    simpa only [Function.comp_def, id_eq] using
      hjoint.comp (continuousOn_const.prodMk continuousOn_id) hmap
  rcases hcompact.bddAbove_image hslice with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hK ⟨x, mem_univ _, rfl⟩

/-- The supremum of the actual full curvature norm is continuous on the compact time slab.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CurvatureSupremum_continuous_of_compact
    (hcompact : IsCompact (Set.univ : Set M)) :
    ContinuousOn (m64CurvatureSupremum F) (Set.Icc a b) := by
  let J : Set ℝ := Set.Icc a b
  let f : J → M → ℝ := fun t x =>
    (F.connection (t : ℝ)).curvatureTensorNorm x
  have hjoint : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).curvatureTensorNorm p.2)
      (J ×ˢ Set.univ) := by
    have h := (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).continuousOn.sqrt
    apply h.congr
    intro p _hp
    dsimp only
    rw [LeviCivitaData.curvatureDerivativeNorm_zero]
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  let q : J × M → (J ×ˢ (Set.univ : Set M)) := fun p =>
    ⟨(p.1.1, p.2), ⟨p.1.2, mem_univ _⟩⟩
  have hq : Continuous q := by
    exact (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk
      (fun _ => ⟨by simp, mem_univ _⟩))
  have huncurry : Continuous (Function.uncurry f) := by
    have hk := hjoint.domRestrict
    have hc := hk.comp hq
    change Continuous (fun p : J × M =>
      (F.connection (p.1 : ℝ)).curvatureTensorNorm p.2)
    simpa [f, q, Function.comp_def] using hc
  have hs := IsCompact.continuous_sSup (f := f) hcompact huncurry
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun t : J => m64CurvatureSupremum F (t : ℝ))
  simpa [f, m64CurvatureSupremum] using hs

/-- The guarded full-curvature supremum is nonnegative, including the empty target range.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CurvatureSupremum_nonneg
    {t : ℝ}
    (hbounded : BddAbove
      (Set.range (fun x : M => (F.connection t).curvatureTensorNorm x))) :
    0 ≤ m64CurvatureSupremum F t := by
  let S : Set ℝ := Set.range (fun x : M => (F.connection t).curvatureTensorNorm x)
  by_cases hS : S.Nonempty
  · obtain ⟨_, x, rfl⟩ := hS
    exact (Real.sqrt_nonneg _).trans (le_csSup hbounded (Set.mem_range_self x))
  · have hEmpty : S = (∅ : Set ℝ) := not_nonempty_iff_eq_empty.mp hS
    rw [show m64CurvatureSupremum F t = sSup S by rfl, hEmpty, Real.sSup_empty]

/-- Every actual pointwise curvature norm lies below the bounded full-curvature supremum.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64Curvature_le_supremum
    {t : ℝ}
    (hbounded : BddAbove
      (Set.range (fun x : M => (F.connection t).curvatureTensorNorm x)))
    (x : M) :
    (F.connection t).curvatureTensorNorm x ≤ m64CurvatureSupremum F t :=
  le_csSup hbounded (Set.mem_range_self x)

end PoincareMT
