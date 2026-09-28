import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCutoff
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Geometry

namespace Geometry

theorem LocallyPiecewiseAffineOn.max {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : E → ℝ} {U : Set E}
    (hf : LocallyPiecewiseAffineOn f U) (hg : LocallyPiecewiseAffineOn g U) :
    LocallyPiecewiseAffineOn (fun x => max (f x) (g x)) U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  obtain ⟨L, hL, hxL, _, hgL⟩ := hg x hx
  obtain ⟨R, hR, hxR, hRKL⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      (isOpen_interior.inter isOpen_interior) (singleton_subset_iff.mpr ⟨hxK, hxL⟩)
  have hRf := (hfK.finitePiecewiseAffineOn hK).restrict R hR
    (fun _ hp => interior_subset (hRKL hp).1)
  have hRg := (hgL.finitePiecewiseAffineOn hL).restrict R hR
    (fun _ hp => interior_subset (hRKL hp).2)
  obtain ⟨T, hT, hTR, hfg⟩ := hRf.max hRg
  refine ⟨T, hT, ?_, ?_, hfg⟩
  · rw [hTR]
    exact hxR (mem_singleton x)
  · rw [hTR]
    exact fun _ hp => hKU (interior_subset (hRKL hp).1)

end Geometry

namespace PLBandCutoff

noncomputable def unionWidth {X Y : Type*} (w : X → ℝ) (v : Y → ℝ) (z : X × Y) : ℝ :=
  max (w z.1) (v z.2)

theorem unionWidth_properties {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (w : X → ℝ) (v : Y → ℝ) (hcw : Continuous w) (hcv : Continuous v)
    (hw : ∀ x, w x ∈ Icc 0 1) (hv : ∀ y, v y ∈ Icc 0 1)
    (U K : Set X) (V L : Set Y)
    (hwo : ∀ x, x ∉ U → w x = 0) (hvo : ∀ y, y ∉ V → v y = 0)
    (hwk : ∀ x ∈ K, w x = 1) (hvl : ∀ y ∈ L, v y = 1) :
    Continuous (unionWidth w v) ∧
      (∀ z, unionWidth w v z ∈ Icc 0 1) ∧
      (∀ z, z ∉ (U ×ˢ univ) ∪ (univ ×ˢ V) → unionWidth w v z = 0) ∧
      ∀ z ∈ (K ×ˢ univ) ∪ (univ ×ˢ L), unionWidth w v z = 1 := by
  refine ⟨(hcw.comp continuous_fst).max (hcv.comp continuous_snd), ?_, ?_, ?_⟩
  · intro z
    exact ⟨(hw z.1).1.trans (le_max_left _ _), max_le (hw z.1).2 (hv z.2).2⟩
  · intro z hz
    have hx : z.1 ∉ U := fun h => hz (Or.inl ⟨h, mem_univ _⟩)
    have hy : z.2 ∉ V := fun h => hz (Or.inr ⟨mem_univ _, h⟩)
    simp only [unionWidth, hwo z.1 hx, hvo z.2 hy, max_self]
  · intro z hz
    rcases hz with hx | hy
    · exact (show max (w z.1) (v z.2) = 1 from
        (congrArg (fun r => max r (v z.2)) (hwk z.1 hx.1)).trans (max_eq_left (hv z.2).2))
    · exact (show max (w z.1) (v z.2) = 1 from
        (congrArg (max (w z.1)) (hvl z.2 hy.2)).trans (max_eq_right (hw z.1).2))

theorem locallyPiecewiseAffineOn_unionWidth
    {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (w : X → ℝ) (v : Y → ℝ)
    (q : E → X) (d : F → Y) {U : Set E} {V : Set F}
    (hw : LocallyPiecewiseAffineOn (w ∘ q) U)
    (hv : LocallyPiecewiseAffineOn (v ∘ d) V) :
    LocallyPiecewiseAffineOn (unionWidth w v ∘ Prod.map q d) (U ×ˢ V) := by
  let a := (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap
  let b := (ContinuousLinearMap.snd ℝ E F).toContinuousAffineMap
  have hUV := hw.isOpen.prod hv.isOpen
  have ha := (hw.comp (locallyPiecewiseAffineOn_affine a isOpen_univ)).mono hUV
    (fun z hz => ⟨mem_univ _, hz.1⟩)
  have hb := (hv.comp (locallyPiecewiseAffineOn_affine b isOpen_univ)).mono hUV
    (fun z hz => ⟨mem_univ _, hz.2⟩)
  exact ha.max hb

end PLBandCutoff
