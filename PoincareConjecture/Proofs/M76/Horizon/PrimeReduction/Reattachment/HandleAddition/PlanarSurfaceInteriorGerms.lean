import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceCarrierInterior
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeChartRestriction









set_option autoImplicit false
open Set Filter Geometry Topology Metric
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_connected_dense_core_neighborhood_of_chart
    {K B : Set P2} {M C : Set V3} (hCM : C ⊆ M)
    (hC : Convex ℝ C) (hMC : M ⊆ closure C)
    (H : OpenPartialHomeomorph K M)
    (hcore : ∀ z ∈ H.source,(H z : V3) ∈ C ↔ (z : P2) ∉ B)
    {x : K} (hx : x ∈ H.source)
    {O : Set P2} (hO : IsOpen O) (hxO : (x : P2) ∈ O) :
    ∃ V : Set P2, IsOpen V ∧ (x : P2) ∈ V ∧ V ⊆ O ∧
      IsPreconnected (V ∩ (K \ B)) ∧ V ∩ K ⊆ closure (V ∩ (K \ B)) := by
  let U : Set K := Subtype.val ⁻¹' O
  have hU : IsOpen U := hO.preimage continuous_subtype_val
  have hHU : IsOpen (H '' (H.source ∩ U)) := H.isOpen_image_source_inter hU
  obtain ⟨W,hW,hWeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hHU
  have hxW : (H x : V3) ∈ W := by
    change H x ∈ Subtype.val ⁻¹' W
    rw [hWeq]
    exact ⟨x,⟨hx,hxO⟩,rfl⟩
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW _ hxW
  let ballM : Set M := Subtype.val ⁻¹' Metric.ball (H x : V3) r
  have hballT : ballM ⊆ H.target := by
    intro y hy
    have hyW : y ∈ Subtype.val ⁻¹' W := hrW hy
    rw [hWeq] at hyW
    obtain ⟨z,hz,rfl⟩ := hyW
    exact H.map_source hz.1
  let Vrel := H.source ∩ H ⁻¹' ballM
  have hVrel : IsOpen Vrel := H.isOpen_inter_preimage (isOpen_ball.preimage continuous_subtype_val)
  obtain ⟨V0,hV0,hV0eq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hVrel
  let V := V0 ∩ O
  have hVeq : (Subtype.val : K → P2) ⁻¹' V = Vrel := by
    apply Subset.antisymm
    · intro y hy
      exact hV0eq.subset hy.1
    · intro y hy
      refine ⟨hV0eq.symm.subset hy,?_⟩
      have hh : H y ∈ H '' (H.source ∩ U) := by
        rw [←hWeq]
        exact hrW hy.2
      obtain ⟨z,hz,hzy⟩ := hh
      exact (H.injOn hz.1 hy.1 hzy) ▸ hz.2
  have hxV : (x : P2) ∈ V := hVeq.symm.subset
    ⟨hx,mem_ball_self hr⟩
  let coreM : Set M := ballM ∩ Subtype.val ⁻¹' C
  have hcoreImage : Subtype.val '' coreM = Metric.ball (H x : V3) r ∩ C := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y,hCM hy.2⟩,hy,rfl⟩
  have hcoreConnected : IsPreconnected coreM := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hcoreImage]
    exact ((convex_ball _ _).inter hC).isPreconnected
  have hcoreEq : (fun z : M => (H.symm z : P2)) '' coreM = V ∩ (K \ B) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzt := hballT hz.1
      have hzs := H.map_target hzt
      have hzV : H.symm z ∈ Vrel := by
        refine ⟨hzs,?_⟩
        change H (H.symm z) ∈ ballM
        rw [H.right_inv hzt]
        exact hz.1
      refine ⟨hVeq.symm.subset hzV,(H.symm z).property,?_⟩
      exact (hcore _ hzs).mp (by rw [H.right_inv hzt]; exact hz.2)
    · rintro ⟨hyV,hyK,hyB⟩
      let z : K := ⟨y,hyK⟩
      have hz := hVeq.subset (show z ∈ Subtype.val ⁻¹' V from hyV)
      refine ⟨H z,⟨hz.2,(hcore z hz.1).mpr hyB⟩,?_⟩
      exact congrArg Subtype.val (H.left_inv hz.1)
  have hcont : ContinuousOn (fun z : M => (H.symm z : P2)) H.target :=
    continuous_subtype_val.comp_continuousOn H.symm.continuousOn
  refine ⟨V,hV0.inter hO,hxV,inter_subset_right,?_,?_⟩
  · rw [←hcoreEq]
    exact hcoreConnected.image _ (hcont.mono (fun _ hz => hballT hz.1))
  · rintro y ⟨hyV,hyK⟩
    let z : K := ⟨y,hyK⟩
    have hz := hVeq.subset (show z ∈ Subtype.val ⁻¹' V from hyV)
    have hcl : H z ∈ closure coreM := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,hcoreImage]
      exact isOpen_ball.inter_closure ⟨hz.2,hMC (H z).property⟩
    have hh := ((hcont.continuousWithinAt (H.map_source hz.1)).mono
      (fun _ hw => hballT hw.1)).mem_closure hcl
      (show MapsTo (fun z : M => (H.symm z : P2)) coreM (V ∩ (K \ B)) from
        fun _ hw => hcoreEq.subset (mem_image_of_mem _ hw))
    simpa only [H.left_inv hz.1] using hh

theorem affine_halfplane_core_dense
    (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3)
    (hu : psi.contLinear u = 1) (hv : ell.contLinear v = 1)
    (hpv : psi.contLinear v = 0) :
    {z | ell z = 0 ∧ 0 ≤ psi z} ⊆ closure {z | ell z = 0 ∧ 0 < psi z} := by
  intro z hz
  let d := u - ell.contLinear u • v
  have hld : ell.contLinear d = 0 := by
    change ell.contLinear (u - ell.contLinear u • v) = 0
    rw [map_sub,map_smul,hv]
    simp
  have hpd : psi.contLinear d = 1 := by
    change psi.contLinear (u - ell.contLinear u • v) = 1
    rw [map_sub,map_smul,hu,hpv]
    simp
  let f : ℝ → V3 := fun t => t • d + z
  have hf : Continuous f := by fun_prop
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simp [closure_Ioi]
  have hm : MapsTo f (Ioi (0 : ℝ)) {z | ell z = 0 ∧ 0 < psi z} := by
    intro t ht
    constructor
    · change ell (t • d + z) = 0
      change ell (t • d +ᵥ z) = 0
      rw [ell.map_vadd,map_smul]
      simp [hld,hz.1]
    · change 0 < psi (t • d + z)
      change 0 < psi (t • d +ᵥ z)
      rw [psi.map_vadd,map_smul]
      simpa [hpd] using add_pos_of_pos_of_nonneg ht hz.2
  have hh := hf.continuousWithinAt.mem_closure hzero hm
  simpa only [f,zero_smul,zero_add] using hh

theorem ChartwisePLSphere.planar_exterior_connected_dense_interior_germs
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0) :
    ∀ x ∈ K.space, ∀ O : Set P2, IsOpen O → x ∈ O →
      ∃ V : Set P2, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
        IsPreconnected (V ∩ (K.space \ B)) ∧
        V ∩ K.space ⊆ closure (V ∩ (K.space \ B)) := by
  classical
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let H0 : K.space ≃ₜ ↥(S ∩ E) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn p K.space hpi)
      (hp.continuousOn.domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hps)
  have hH0 (z : K.space) : (H0 z : X) = p z := rfl
  intro x hx O hO hxO
  have hxSE := hps.subset (mem_image_of_mem p hx)
  obtain ⟨T,hxT,_,hcase⟩ := s.surface_rim_charts_of_frontier_crossings he hcross (p x) hxSE
  have transport (M C : Set V3) (hCM : C ⊆ M) (hC : Convex ℝ C)
      (hdense : M ⊆ closure C)
      (hlocal : ∀ y ∈ T.source,y ∈ S ∩ E ↔ T y ∈ M)
      (hcore : ∀ y ∈ T.source,y ∈ S ∩ E →
        (T y ∈ C ↔ y ∉ frontier E)) :
      ∃ V : Set P2, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
        IsPreconnected (V ∩ (K.space \ B)) ∧
        V ∩ K.space ⊆ closure (V ∩ (K.space \ B)) := by
    have himage : T.IsImage (S ∩ E) M := fun _ hy => (hlocal _ hy).symm
    obtain ⟨r,hrs,_,hrval,_⟩ := himage.exists_subtype_chart ⟨p x,hxSE⟩ hxT
    let H := H0.toOpenPartialHomeomorph.trans r
    have hxH : (⟨x,hx⟩ : K.space) ∈ H.source := by
      exact ⟨mem_univ _,hrs.symm.subset hxT⟩
    have hval (z : K.space) (hz : z ∈ H.source) : (H z : V3) = T (p z) :=
      hrval (H0 z) hz.2
    apply exists_connected_dense_core_neighborhood_of_chart hCM hC hdense H ?_ hxH hO hxO
    intro z hz
    rw [hval z hz]
    have hzT : p z ∈ T.source := hrs.subset hz.2
    exact (hcore (p z) hzT (hps.subset (mem_image_of_mem p z.property))).trans
      (not_congr (hproper z z.property))
  rcases hcase with ⟨ell,v,_,hlocal,hdis⟩ | ⟨ell,psi,u,v,hu,hv,hpv,hlocal,hrim⟩
  · let M : Set V3 := {z | ell z = 0}
    have hM : Convex ℝ M := (convex_singleton (0 : ℝ)).affine_preimage ell.toAffineMap
    apply transport M M subset_rfl hM subset_closure hlocal
    intro y hy hySE
    have hm := (hlocal y hy).mp hySE
    have hn : y ∉ frontier E := fun hf => disjoint_left.mp hdis hy ⟨hySE.1,hf⟩
    exact iff_of_true hm hn
  · let M : Set V3 := {z | ell z = 0 ∧ 0 ≤ psi z}
    let C : Set V3 := {z | ell z = 0 ∧ 0 < psi z}
    have hCM : C ⊆ M := fun _ hz => ⟨hz.1,hz.2.le⟩
    have hC : Convex ℝ C :=
      ((convex_singleton (0 : ℝ)).affine_preimage ell.toAffineMap).inter
        ((convex_Ioi (0 : ℝ)).affine_preimage psi.toAffineMap)
    apply transport M C hCM hC (affine_halfplane_core_dense ell psi u v hu hv hpv) hlocal
    intro y hy hySE
    have hm := (hlocal y hy).mp hySE
    constructor
    · intro hz hf
      have hh := (hrim y hy).mp ⟨hySE.1,hf⟩
      exact (ne_of_gt hz.2) hh.2
    · intro hn
      refine ⟨hm.1,lt_of_le_of_ne hm.2 ?_⟩
      intro hh
      exact hn ((hrim y hy).mpr ⟨hm.1,hh.symm⟩).2

end PoincareConjecture.M76
