import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalRegionPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDomainBoundaryCollar



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_collar_region_PL_motion
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X} (he : PLDomain e R)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {eps delta : ℝ} (heps : 0 < eps) (hed : eps < delta)
    (c : E × ℝ → X)
    (hcPL : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) delta))
    (hemb : IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) delta) => c z))
    (hmap : MapsTo c (K.space ×ˢ Icc (0 : ℝ) delta) R)
    (hopenSmall : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) eps))))
    (hopenLarge : IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) delta))))
    (HB : K.space ≃ₜ frontier R) (hbase : ∀ x : K.space, c (x, 0) = HB x)
    (H : I → K.space ≃ₜ K.space)
    (hc : Continuous (fun z : I × K.space => H z.1 z.2))
    (hci : Continuous (fun z : I × K.space => (H z.1).symm z.2))
    (hzero : ∀ x, H 0 x = x)
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hvalue : ∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (H t x : E)) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ t : I, ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
        (G t ⟨c z, hmap ⟨z.property.1, z.property.2.1, z.property.2.2.trans hed.le⟩⟩ : X) =
          c (scaledCollarExtension heps H hc hci t z)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G t x = x) ∧
      (∀ t : I, ∀ x : K.space,
        (G t ⟨HB x, he.closed.frontier_subset (HB x).property⟩ : X) = HB (H t x)) ∧
      (∀ t : I, ∀ x : K.space,
        G t ⟨c (x, eps), hmap ⟨x.property, heps.le, hed.le⟩⟩ =
          ⟨c (x, eps), hmap ⟨x.property, heps.le, hed.le⟩⟩) := by
  have hsub : K.space ×ˢ Icc (0 : ℝ) eps ⊆ K.space ×ˢ Icc (0 : ℝ) delta :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hed.le⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK heps
  have hcSmall : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) eps) := by
    have h := hcPL.restrict_finite J hJ (hJs.subset.trans hsub)
    exact hJs ▸ h
  obtain ⟨G, hG, hGi, hGzero, hsmall, hsmalli, hout, houter, hinner⟩ :=
    exists_original_collar_region_motion e K hK heps c hcSmall
      (hemb.comp (IsEmbedding.inclusion hsub)) (hmap.mono_left hsub) hopenSmall
      H hc hci hzero track htrack hvalue
  have hfront : frontier R ⊆ c '' (K.space ×ˢ Icc (0 : ℝ) eps) := by
    intro x hx
    obtain ⟨z, hz⟩ := HB.surjective ⟨x, hx⟩
    exact ⟨(z, 0), ⟨z.property, le_rfl, heps.le⟩,
      (hbase z).trans (congrArg Subtype.val hz)⟩
  refine ⟨G, hG, hGi, hGzero, ?_, hsmall, hout, ?_, hinner⟩
  · intro t
    have hm := isFinitePL_scaledCollarExtension heps H hc hci track htrack hvalue t
    refine ⟨chartwisePL_original_collar_region_motion e he K hK heps hed c hcPL hemb hmap
      hopenLarge hfront ⟨G t, (G t).continuous⟩ _ hm (hsmall t) (hout t), ?_⟩
    apply chartwisePL_original_collar_region_motion e he K hK heps hed c hcPL hemb hmap
      hopenLarge hfront ⟨(G t).symm, (G t).symm.continuous⟩ _ hm.symm (hsmalli t)
    intro x hx
    change (G t).symm x = x
    apply (G t).injective
    rw [(G t).apply_symm_apply, hout t x hx]
  · intro t x
    have hx : (⟨c (x, 0), hmap (hsub ⟨x.property, le_rfl, heps.le⟩)⟩ : R) =
        ⟨HB x, he.closed.frontier_subset (HB x).property⟩ := Subtype.ext (hbase x)
    have h := houter t x
    rw [hx, hbase] at h
    exact h

theorem exists_prepared_original_boundary_collar_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∃ (s : Finset R) (K : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : K.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X) (delta : ℝ),
      K.faces.Finite ∧ 0 < delta ∧ delta ≤ 1 / 2 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) delta) ∧
      IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) delta) => c z) ∧
      MapsTo c (K.space ×ˢ Icc (0 : ℝ) delta) R ∧
      MapsTo c (K.space ×ˢ Icc (0 : ℝ) delta) U ∧
      (∀ x : K.space, c (x, 0) = HB x) ∧
      ∀ (H : I → K.space ≃ₜ K.space)
        (_hc : Continuous (fun z : I × K.space => H z.1 z.2))
        (_hci : Continuous (fun z : I × K.space => (H z.1).symm z.2))
        (_hzero : ∀ x, H 0 x = x)
        (track : (ℝ × (s → ℝ × V3)) → (s → ℝ × V3)),
        FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space) →
        (∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (H t x : s → ℝ × V3)) →
        ∃ G : I → R ≃ₜ R,
          Continuous (fun z : I × R => G z.1 z.2) ∧
          Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
          (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
          (∀ t : I, ∀ x : K.space,
            (G t ⟨HB x, he.closed.frontier_subset (HB x).property⟩ : X) = HB (H t x)) ∧
          (∀ t : I, ∀ x : R, (x : X) ∉ U → G t x = x) ∧
          (∀ t : I, ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) (delta / 2)) → G t x = x) ∧
          (∀ t : I, ∀ x : R, (x : X) ∈ c '' (K.space ×ˢ {delta / 2}) → G t x = x) := by
  classical
  obtain ⟨s, K, HB, c, hK, hcPL, hemb, hmap, hbase, _, delta, hd, hdhalf, hsmallU, hopen⟩ :=
    he.exists_small_boundary_collar_of_interior_nonempty hR hne hU hBU
  have hd1 : delta ≤ 1 := by linarith
  have hdsub : K.space ×ˢ Icc (0 : ℝ) delta ⊆ K.space ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hd1⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK hd
  have hcDelta : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) delta) := by
    have h := hcPL.restrict_finite J hJ (hJs.subset.trans hdsub)
    exact hJs ▸ h
  have hiDelta := hemb.comp (IsEmbedding.inclusion hdsub)
  have hmDelta := hmap.mono_left hdsub
  refine ⟨s, K, HB, c, delta, hK, hd, hdhalf, hcDelta, hiDelta, hmDelta, hsmallU, hbase, ?_⟩
  intro H hc hci hzero track htrack hvalue
  have heps : 0 < delta / 2 := half_pos hd
  have hepsDelta : delta / 2 < delta := half_lt_self hd
  obtain ⟨G, hG, hGi, hGzero, hGPL, _, hout, houter, hinner⟩ :=
    exists_original_collar_region_PL_motion e he K hK heps hepsDelta c hcDelta hiDelta hmDelta
      (hopen _ heps hepsDelta.le) (hopen _ hd le_rfl) HB hbase
      H hc hci hzero track htrack hvalue
  refine ⟨G, hG, hGi, hGzero, hGPL, houter, ?_, hout, ?_⟩
  · intro t x hx
    apply hout t x
    rintro ⟨z, hz, hzx⟩
    exact hx (hzx ▸ hsmallU ⟨hz.1, hz.2.1, hz.2.2.trans hepsDelta.le⟩)
  · intro t x hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hzval : z = (z.1, delta / 2) := Prod.ext rfl hz.2
    have hxval : (⟨c ((⟨z.1, hz.1⟩ : K.space), delta / 2),
        hmDelta ⟨hz.1, heps.le, hepsDelta.le⟩⟩ : R) = x := by
      apply Subtype.ext
      exact (congrArg c hzval).symm.trans hzx
    have h := hinner t ⟨z.1, hz.1⟩
    rw [hxval] at h
    exact h

end PoincareConjecture.M76.CollarIsotopy
