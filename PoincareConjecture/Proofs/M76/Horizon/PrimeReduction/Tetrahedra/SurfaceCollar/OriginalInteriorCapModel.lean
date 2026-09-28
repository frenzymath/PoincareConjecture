import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalProductFiniteCoordinates

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_finite_cap_model
    {X E A ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {T : Set E} (hTK : T ⊆ K.space)
    {D q : Set A} {p : A → X} {S : Set X}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D q)
    (hp : PolyhedralPLInCharts e p D) (hpi : InjOn p D)
    (hpT : p '' D ⊆ g '' T) (hproper : (p '' D) ∩ S = p '' q) :
    ∃ d r : Set E, IsFinitePLBallPair (ℝ × ℝ) d r ∧ d ⊆ T ∧
      g '' d = p '' D ∧ g '' r = p '' q ∧ d ∩ g ⁻¹' S = r ∧
      d = K.space ∩ g ⁻¹' (p '' D) ∧ r = K.space ∩ g ⁻¹' (p '' q) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let H := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    H.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  have hpK : MapsTo p D (g '' K.space) :=
    fun z hz => image_mono hTK (hpT (mem_image_of_mem p hz))
  let f : A → E := fun z => if hz : z ∈ D then pr.symm ⟨p z,hpK hz⟩ else 0
  have hfval (z : D) : f z = (pr.symm ⟨p z,hpK z.property⟩ : E) := by
    simp only [f,dif_pos z.property]
  have hfK : MapsTo f D K.space := by
    intro z hz
    rw [hfval ⟨z,hz⟩]
    exact (pr.symm ⟨p z,hpK hz⟩).property
  have hvalue (z : A) (hz : z ∈ D) : g (f z) = p z := by
    rw [hfval ⟨z,hz⟩]
    exact congrArg Subtype.val (pr.apply_symm_apply ⟨p z,hpK hz⟩)
  have hfc : ContinuousOn f D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := continuous_subtype_val.comp (pr.symm.continuous.comp
      (hp.continuousOn.domRestrict.subtype_mk (fun z => hpK z.property)))
    convert hc using 1
    funext z
    exact hfval z
  obtain ⟨M,_,hM,hMs,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hf : FinitePiecewiseAffineOn f D := by
    rw [←hMs]
    exact hg.finitePiecewiseAffineOn_lift he hgi M hM
      (hfc.mono hMs.subset) (fun z hz => hfK (hMs.subset hz))
      ((hp.restrict_finite M hM hMs.subset).congr (fun z hz => (hvalue z (hMs.subset hz)).symm))
  have hfi : InjOn f D := by
    intro z hz w hw heq
    exact hpi hz hw ((hvalue z hz).symm.trans ((congrArg g heq).trans (hvalue w hw)))
  have hsource (U : Set A) (hUD : U ⊆ D) :
      f '' U = K.space ∩ g ⁻¹' (p '' U) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨hfK (hUD hz),⟨z,hz,(hvalue z (hUD hz)).symm⟩⟩
    · rintro x ⟨hx,z,hz,hzx⟩
      exact ⟨z,hz,hgi (hfK (hUD hz)) hx ((hvalue z (hUD hz)).trans hzx)⟩
  have himage (U : Set A) (hUD : U ⊆ D) : g '' (f '' U) = p '' U := by
    rw [←image_comp]
    exact image_congr (fun z hz => hvalue z (hUD hz))
  refine ⟨f '' D,f '' q,hD.image hf hfi,?_,himage D Subset.rfl,himage q hD.1,?_,
    hsource D Subset.rfl,hsource q hD.1⟩
  · rintro _ ⟨z,hz,rfl⟩
    obtain ⟨x,hx,hxz⟩ := hpT (mem_image_of_mem p hz)
    exact hgi (hTK hx) (hfK hz) (hxz.trans (hvalue z hz).symm) ▸ hx
  · rw [hsource D Subset.rfl,hsource q hD.1,←hproper,preimage_inter]
    ext x
    simp only [mem_inter_iff,mem_preimage]
    tauto

end PoincareConjecture.M76
