import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ThreeTorusPunctureEnd
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs

/-!
# The actual chart-puncture end in Wall's quantified form

The checked compact puncture cores are transported along an actual
embedding onto the puncture complement. Their simply connected
complements give exactly the protected based nullhomotopies required
by the named end predicate. See Hamilton 1976, p.66 and derivation331.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- A compact chart puncture supplies the exact one-end predicate on
any explicitly marked copy of its complement. The ambient chart need
not be PL in the eventual pulled-back atlas. See derivation331. -/
theorem hasOneSimplyConnectedEnd_of_chart_puncture
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] (Q : OpenPartialHomeomorph E X)
    (h0 : (0 : E) ∈ Q.source) (hdim : 2 < Module.finrank ℝ E)
    (j : Y → X) (hj : Topology.IsEmbedding j) (hjrange : range j = {Q 0}ᶜ) :
    HasOneSimplyConnectedEnd Y := by
  intro C hC
  have hA : IsCompact (j '' C) := hC.image hj.continuous
  have hqA : Q 0 ∉ j '' C := by
    intro hq
    have hr : Q 0 ∈ range j := image_subset_range j C hq
    rw [hjrange] at hr
    exact hr (mem_singleton _)
  obtain ⟨K, hK, hAK, hqK, hsc⟩ :=
    Q.exists_compact_core_simplyConnected_punctured_complement hdim h0 hA hqA
  let D : Set Y := j ⁻¹' K
  have hKrange : K ⊆ range j := by
    rw [hjrange]
    intro x hx
    exact fun heq => hqK ((mem_singleton_iff.mp heq) ▸ hx)
  have hD : IsCompact D := hj.isInducing.isCompact_preimage' hK hKrange
  have hCD : C ⊆ interior D := by
    intro x hx
    apply (isOpen_interior.preimage hj.continuous).subset_interior_iff.mpr
      (preimage_mono interior_subset)
    exact hAK (mem_image_of_mem j hx)
  have hcomplement : j '' Dᶜ = Kᶜ \ {Q 0} := by
    change j '' (j ⁻¹' K)ᶜ = Kᶜ \ {Q 0}
    rw [← preimage_compl, image_preimage_eq_inter_range, hjrange]
    rfl
  have hDsc : IsSimplyConnected Dᶜ := by
    apply hj.isSimplyConnected_image.mp
    rw [hcomplement]
    exact hsc
  refine ⟨D, hD, hCD, hDsc.isPathConnected.isConnected, ?_⟩
  intro x p hp
  obtain ⟨H, hH⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hDsc).2 x p hp
  refine ⟨H, fun z hz => ?_⟩
  exact hH z (interior_subset (hCD hz))

/-- The literal period64 punctured three-torus satisfies Wall's exact
end predicate. Its puncture is the same half-period point as in the
checked immersion. See Hamilton p.66 and derivation331. -/
theorem zero_punctured_torus_hasOneSimplyConnectedEnd :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    HasOneSimplyConnectedEnd
      ({p}ᶜ : Set ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ))
  have h0 : (0 : CubeShell.Ambient) ∈ Q.source := by
    rw [AddCircle.centeredCubeQuotient_source]
    norm_num
  apply hasOneSimplyConnectedEnd_of_chart_puncture Q h0
    (by norm_num [CubeShell.Ambient, Module.finrank_prod])
    (Subtype.val : ({Q 0}ᶜ : Set _) → _) Topology.IsEmbedding.subtypeVal
  exact Subtype.range_coe

/-- The whole-domain subtype used by `HasWallCompactCore` has the same
literal puncture end. The embedding is the composite of the two actual
subtype inclusions. See Hamilton p.66 and derivation331. -/
theorem zero_punctured_torus_domain_hasOneSimplyConnectedEnd :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    let Y := ({p}ᶜ : Set ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle))
    HasOneSimplyConnectedEnd (univ : Set Y) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ))
  let Y := ({Q 0}ᶜ : Set ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle))
  have h0 : (0 : CubeShell.Ambient) ∈ Q.source := by
    rw [AddCircle.centeredCubeQuotient_source]
    norm_num
  apply hasOneSimplyConnectedEnd_of_chart_puncture Q h0
    (by norm_num [CubeShell.Ambient, Module.finrank_prod])
    (fun x : (univ : Set Y) => ((x : Y) : _))
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (y : Y).property
  · intro hx
    exact ⟨⟨⟨x, hx⟩, mem_univ _⟩, rfl⟩

end PoincareMT.M76
