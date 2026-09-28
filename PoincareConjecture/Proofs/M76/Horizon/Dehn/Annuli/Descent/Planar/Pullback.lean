import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.Decomposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.RetainedReparametrization

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_ordinary_finitePL_pullback
    {E Y X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    {S : Set E} {T : Set Y} {R : Set X} {f : E → X}
    (H : T ≃ₜ S) (hH : H.IsFinitePL)
    (hf : PolyhedralPLInCharts e f S) (hfR : MapsTo f S R)
    (M : SourceCircleDecomposition f S)
    (hinterior : MapsTo f (doubleLocusOn f S) (interior R))
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (hunique : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z) :
    ∃ g : Y → X,
      (∀ x : T, g x = f (H x)) ∧
      PolyhedralPLInCharts e g T ∧ MapsTo g T R ∧
      IsLocallyInjective (fun x : T ↦ g x) ∧
      IsCompact (doubleLocusOn g T) ∧
      MapsTo g (doubleLocusOn g T) (interior R) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g T R x y)) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
        x ≠ y → x ≠ z → g x = g y → g x = g z → y = z) ∧
      Nonempty (SourceCircleDecomposition g T) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g T)) =
        Nat.card (ConnectedComponents (doubleLocusOn f S)) := by
  classical
  obtain ⟨F, hF, hFvalue⟩ := hH
  let g := f ∘ F
  have hvalue (x : T) : g x = f (H x) := congrArg f (hFvalue x).symm
  have hmap : MapsTo F T S := by
    intro x hx
    rw [← hFvalue ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hF' := hF
  obtain ⟨K, hK, hKT, _⟩ := hF'
  have hg : PolyhedralPLInCharts e g T := by
    have hh := hf.comp_finitePiecewiseAffineOn K hK
      (by simpa only [hKT] using hF) (fun x hx ↦ hmap (hKT.subset hx))
    simpa only [hKT] using hh
  have hgR : MapsTo g T R := fun x hx ↦ hfR (hmap hx)
  have hT : IsCompact T := hKT ▸ K.isCompact_space_of_finite hK
  have hS : IsCompact S := by
    have him : (fun x : T ↦ (H x : E)) '' univ = S := by
      ext x
      constructor
      · rintro ⟨y, _, rfl⟩
        exact (H y).property
      · intro hx
        exact ⟨H.symm ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (H.apply_symm_apply _)⟩
    let := isCompact_iff_compactSpace.mp hT
    exact him ▸ isCompact_univ.image (continuous_subtype_val.comp H.continuous)
  have hgd : IsCompact (doubleLocusOn g T) := by
    have hd : IsCompact (doubleLocusOn f S) :=
      M.space ▸ M.graph.isCompact_space_of_finite M.finite
    let := isCompact_iff_compactSpace.mp hd
    let D := doubleLocusOnSourceHomeomorph H hvalue
    let : CompactSpace (doubleLocusOn g T) := D.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hgi : MapsTo g (doubleLocusOn g T) (interior R) := by
    intro x hx
    rw [hvalue ⟨x, hx.1⟩]
    exact hinterior ((doubleLocusOn_source_homeomorph_iff H hvalue ⟨x, hx.1⟩).mp hx)
  have hgu : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
      x ≠ y → x ≠ z → g x = g y → g x = g z → y = z := by
    intro x hx y hy z hz hxy hxz hxyv hxzv
    have hne (a b : T) (hab : (a : Y) ≠ b) : (H a : E) ≠ H b := by
      intro hh
      exact hab (congrArg Subtype.val (H.injective (Subtype.ext hh)))
    have hh := hunique (H ⟨x, hx⟩) (H ⟨x, hx⟩).property
      (H ⟨y, hy⟩) (H ⟨y, hy⟩).property (H ⟨z, hz⟩) (H ⟨z, hz⟩).property
      (hne _ _ hxy) (hne _ _ hxz)
      ((hvalue ⟨x, hx⟩).symm.trans (hxyv.trans (hvalue ⟨y, hy⟩)))
      ((hvalue ⟨x, hx⟩).symm.trans (hxzv.trans (hvalue ⟨z, hz⟩)))
    exact congrArg Subtype.val (H.injective (Subtype.ext hh))
  let p : doubleLocusOn f S → doubleLocusOn f S := fun x ↦
    ⟨M.partner ⟨x, M.space.symm.subset x.property⟩,
      M.space.subset (M.partner ⟨x, M.space.symm.subset x.property⟩).property⟩
  have hpu (x : doubleLocusOn f S) (y : E) (hy : y ∈ S)
      (hxy : f x = f y) (hne : (x : E) ≠ y) : y = (p x : E) :=
    M.unique ⟨x, M.space.symm.subset x.property⟩ y hy hne hxy
  have hraw : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → g x = g y →
      Nonempty (RawSourceCrossing e g T R x y) := by
    have hh := raw_source_crossings_of_retained_open_copy hS hT
      (Subset.refl S) (Subset.refl T)
      (by simp) (by simp)
      hf.continuousOn hg.continuousOn H.symm
      (fun x ↦ (hvalue (H.symm x)).trans (congrArg (fun z : S ↦ f z) (H.apply_symm_apply x)))
      p hpu (fun _ hx ↦ hx.1) (fun x hx y hy hxy hne ↦ hcross x hx y hy hne hxy)
    exact fun x hx y hy hne hxy ↦ hh x hx y hy hxy hne
  have hnext : Nonempty (SourceCircleDecomposition g T) := by
    rw [← hKT]
    exact nonempty_sourceCircleDecomposition he K hK
      (by simpa only [hKT] using hg) (by simpa only [hKT] using hgR)
      (by simpa only [hKT] using hgd.isClosed) (by simpa only [hKT] using hgi)
      (by simpa only [hKT] using hraw) (by simpa only [hKT] using hgu)
  exact ⟨g, hvalue, hg, hgR, isLocallyInjective_of_raw_source_crossings hgd.isClosed hraw,
    hgd, hgi, hraw, hgu, hnext, double_component_count_source_homeomorph H hvalue⟩

end PoincareConjecture.M76.Dehn.Annuli
