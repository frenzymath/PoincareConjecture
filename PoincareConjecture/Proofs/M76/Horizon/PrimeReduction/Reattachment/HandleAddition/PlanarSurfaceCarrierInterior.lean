import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms
import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior










set_option autoImplicit false
open Set Filter Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem mem_interior_planar_carrier_of_surface_chart
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (H : K.space ≃ₜ S) (p : P2 → X) (hH : ∀ z : K.space,(H z : X)=p z)
    (hp : PolyhedralPLInCharts e p K.space)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (hv : ell.contLinear v=1)
    (hlocal : ∀ y∈Q.source,y∈S ↔ ell (Q y)=0)
    {x : P2} (hx : x∈K.space) (hxQ : p x∈Q.source) : x∈interior K.space := by
  classical
  have hell : ell.toAffineMap.linear≠0 := by
    intro h
    have hval : ell.toAffineMap.linear v=1 := hv
    rw [h,LinearMap.zero_apply] at hval
    exact zero_ne_one hval
  obtain ⟨a,r,hra,har,haz⟩ :=
    ell.toAffineMap.exists_zeroLevel_coordinates (F := P2) hell (by simp)
  obtain ⟨N,W,hN,hNK,hW,hxW,hWN,hNQ,hcoords⟩ :=
    hp.exists_finite_compatible_chart_patch K hK Q hQ ⟨x,hx⟩ hxQ
  have hxN : x∈N.space := hWN ⟨⟨x,hx⟩,hxW,rfl⟩
  have hpS (z : P2) (hz : z∈K.space) : p z∈S :=
    (hH ⟨z,hz⟩) ▸ (H ⟨z,hz⟩).property
  have hzero (z : P2) (hz : z∈N.space) : ell (Q (p z))=0 :=
    (hlocal _ (hNQ hz)).mp (hpS z (hNK hz))
  let f : P2 → P2 := r ∘ Q ∘ p
  have hf : FinitePiecewiseAffineOn f N.space := hcoords.postcomp r
  have hfi : InjOn f N.space := by
    intro z hz w hw hzw
    have hQeq : Q (p z)=Q (p w) := by
      rw [←har (hzero z hz),←har (hzero w hw)]
      exact congrArg a hzw
    have hpeq := Q.injOn (hNQ hz) (hNQ hw) hQeq
    have hHeq : H ⟨z,hNK hz⟩=H ⟨w,hNK hw⟩ := by
      apply Subtype.ext
      simpa only [hH] using hpeq
    exact congrArg Subtype.val (H.injective hHeq)
  have hHW := H.isOpenMap.image_mem_nhds (hW.mem_nhds hxW)
  obtain ⟨U,hU,hUS⟩ := (mem_nhds_subtype S (H ⟨x,hx⟩) (H '' W)).mp hHW
  obtain ⟨O,hOU,hO,hxO⟩ := mem_nhds_iff.mp hU
  let V : Set P2 := a ⁻¹' (Q '' (Q.source∩O))
  have hV : IsOpen V := (Q.isOpen_image_source_inter hO).preimage a.continuous
  have hxV : f x∈V := by
    change a (r (Q (p x)))∈Q '' (Q.source∩O)
    rw [har (hzero x hxN)]
    exact ⟨p x,⟨hxQ,by simpa only [hH] using hxO⟩,rfl⟩
  have hVsub : V⊆f '' N.space := by
    intro z hz
    obtain ⟨y,⟨hyQ,hyO⟩,hya⟩ := hz
    have hyS : y∈S := (hlocal y hyQ).mpr (by rw [hya]; exact haz z)
    obtain ⟨w,hwW,hwH⟩ := hUS
      (show (⟨y,hyS⟩ : S)∈Subtype.val ⁻¹' U from hOU hyO)
    refine ⟨w,hWN ⟨w,hwW,rfl⟩,?_⟩
    have hwy : p w=y := by
      rw [←hH w]
      exact congrArg Subtype.val hwH
    change r (Q (p w))=z
    rw [hwy,hya,hra]
  obtain ⟨F,hF,hFval⟩ := hf.exists_homeomorph_image hfi
  have hximage : f x∈interior (f '' N.space) :=
    interior_mono hVsub (hV.interior_eq.symm ▸ hxV)
  have hxFN : (F ⟨x,hxN⟩ : P2)∈interior (f '' N.space) := by
    rw [hFval]
    exact hximage
  exact interior_mono hNK ((hF.mem_interior_iff rfl ⟨x,hxN⟩).mp hxFN)

theorem ChartwisePLSphere.planar_exterior_interior_of_not_rim
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space=S∩E)
    (hproper : ∀ z∈K.space,p z∈frontier E ↔ z∈B) :
    K.space\B⊆interior K.space := by
  intro x hx
  have hxSE := hps.subset (mem_image_of_mem p hx.1)
  have hxint : p x∈interior E := (mem_interior_iff_notMem_frontier hxSE.2).mpr
    (fun h => hx.2 ((hproper x hx.1).mp h))
  obtain ⟨G,hxG,hG0,hGe,hGS⟩ := s.exists_pair_chart he.compatible
    (fun y _ => he.cover y) hxSE.1
  obtain ⟨T,hxT,_,_,hTG,_,hdis,hval,_⟩ :=
    G.exists_convex_target_avoiding hxG hG0 (isOpen_interior (s := E)).isClosed_compl
      (by simpa only [mem_compl_iff,not_not] using hxint)
  have hTe (i : α) : (e i).symm.trans T∈piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (hGe i).1.mono ((e i).symm.trans T).open_source
      (fun _ hz => ⟨hz.1,hTG hz.2⟩)
    exact h.congr (fun z _ => (hval ((e i).symm z)).symm)
  have hTint (y : X) (hy : y∈T.source) : y∈interior E := by
    by_contra hn
    exact disjoint_left.mp hdis hy hn
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let H : K.space ≃ₜ ↥(S∩E) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn p K.space hpi)
      (hp.continuousOn.domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hps)
  apply mem_interior_planar_carrier_of_surface_chart K hK H p (fun _ => rfl) hp T hTe
    (ContinuousLinearMap.proj 0).toContinuousAffineMap (Pi.single 0 1) (by simp) ?_ hx.1 hxT
  intro y hy
  change (y∈S ∧ y∈E) ↔ T y 0=0
  rw [and_iff_left (interior_subset (hTint y hy)),hval]
  exact hGS y (hTG hy)

end PoincareConjecture.M76

