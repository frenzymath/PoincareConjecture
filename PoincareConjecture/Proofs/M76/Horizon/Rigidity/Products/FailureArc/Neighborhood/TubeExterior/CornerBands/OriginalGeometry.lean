import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.PanelMaps



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

theorem original_lateral_decomposition
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) :
    (⋃ i, U.map '' band r δ i) ∪ (⋃ i, U.map '' panel r δ i) = U.map '' lateral r ∧
      (U.map '' lateral r) \ (⋃ i, U.map '' openBand r δ i) = ⋃ i, U.map '' panel r δ i ∧
      (∀ i j, (U.map '' band r δ i) ∩ (U.map '' panel r δ j) =
        if incident i j then U.map '' ({seamPoint r δ i j.1} ×ˢ Icc (0 : ℝ) 1) else ∅) ∧
      Pairwise (fun i j : Bool × Bool => Disjoint (U.map '' panel r δ i) (U.map '' panel r δ j)) := by
  have hlat : lateral r ⊆ tube := (lateral_subset r).trans (closedTube_subset hr1)
  have hband (i : Bool × Bool) : band r δ i ⊆ tube :=
    (band_subset_lateral hδ.le hδr.le i).trans hlat
  have hpanel (i : Bool × Bool) : panel r δ i ⊆ tube :=
    (panel_subset_lateral hδ hδr i).trans hlat
  have hinj : InjOn U.map tube := fun z hz w hw h => congrArg Subtype.val
    (U.embedding.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) h)
  refine ⟨?_,?_,?_,?_⟩
  · rw [← lateral_cover hδ hδr,image_union,image_iUnion,image_iUnion]
  · have ho : (⋃ i, openBand r δ i) ⊆ lateral r := by
      apply iUnion_subset
      intro i
      exact (prod_mono (openFootprint_subset r δ i) Subset.rfl).trans
        (band_subset_lateral hδ.le hδr.le i)
    have hh := ((hinj.mono hlat).image_sdiff (t := ⋃ i, openBand r δ i)).symm
    have himage : (U.map '' lateral r) \ U.map '' (⋃ i, openBand r δ i) =
        U.map '' (lateral r \ (⋃ i, openBand r δ i)) := by
      simpa only [inter_eq_right.mpr ho] using hh
    rw [image_iUnion] at himage
    rw [himage,lateral_sdiff_openBands hδ hδr,image_iUnion]
  · intro i j
    rw [← hinj.image_inter (hband i) (hpanel j),band_inter_panel hδ hδr]
    by_cases hij : incident i j
    · rw [if_pos hij,if_pos hij]
    · rw [if_neg hij,if_neg hij,image_empty]
  · intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,hwz⟩
    have heq : w = z := hinj (hpanel j hw) (hpanel i hz) hwz
    exact disjoint_left.mp (panels_pairwise_disjoint hδ hδr hij) hz (heq ▸ hw)

theorem original_lateral_end_planes
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr1 : r ≤ 1) {A : Set P2} (hA : A ⊆ frontier (transverseSquare r)) :
    (U.map '' (A ×ˢ Icc (0 : ℝ) 1)) ∩ frontier R = U.map '' (A ×ˢ ({0,1} : Set ℝ)) := by
  have hsub : A ×ˢ Icc (0 : ℝ) 1 ⊆ tube :=
    (prod_mono hA Subset.rfl).trans ((lateral_subset r).trans (closedTube_subset hr1))
  ext x
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hf⟩
    exact ⟨z,⟨hz.1,(U.frontier_iff z (hsub hz)).mp hf⟩,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    have ht : z.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hz.2 with h | h <;> rw [show z.2 = _ from h] <;> norm_num
    exact ⟨⟨z,⟨hz.1,ht⟩,rfl⟩,(U.frontier_iff z (hsub ⟨hz.1,ht⟩)).mpr hz.2⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
