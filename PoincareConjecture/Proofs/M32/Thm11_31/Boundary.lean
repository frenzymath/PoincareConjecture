import PoincareConjecture.Proofs.M32.Thm11_31.Topology
import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private theorem exists_injOn_nhds
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace V M] [ChartedSpace W N] {f : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ f x)
    (hbij : Function.Bijective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) f x)) :
    ∃ U ∈ 𝓝 x, InjOn f U := by
  classical
  let c := extChartAt 𝓘(ℝ, V) x
  let A := writtenInExtChartAt 𝓘(ℝ, V) 𝓘(ℝ, W) x f
  have hA : ContDiffAt ℝ 1 A (c x) := by
    simpa [A, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))).2
  have hderiv : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) f x = fderiv ℝ A (c x) := by
    change (if MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) f x then
      fderivWithin ℝ A (range 𝓘(ℝ, V)) (c x) else (0 : V →L[ℝ] W)) = _
    rw [if_pos (hf.mdifferentiableAt (by simp))]
    simp [A, c]
  have hAbij : Function.Bijective (fderiv ℝ A (c x)) := by rwa [hderiv] at hbij
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ A (c x))
    (LinearMap.ker_eq_bot.mpr hAbij.1) (LinearMap.range_eq_top.mpr hAbij.2)
  have hstrict : HasStrictFDerivAt A (L : V →L[ℝ] W) (c x) :=
    hA.hasStrictFDerivAt' (hA.differentiableAt (by norm_num)).hasFDerivAt (by norm_num)
  let e := hstrict.toOpenPartialHomeomorph A
  refine ⟨c.source ∩ c ⁻¹' e.source, inter_mem (extChartAt_source_mem_nhds x)
    ((continuousAt_extChartAt x).preimage_mem_nhds
      (e.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source)), ?_⟩
  intro y hy z hz heq
  apply c.injOn hy.1 hz.1
  apply e.injOn hy.2 hz.2
  change A (c y) = A (c z)
  simp only [A, writtenInExtChartAt, Function.comp_apply]
  rw [c.left_inv hy.1, c.left_inv hz.1, heq]

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem horn_boundary_sphere_subset_carrier (horn : StrongHorn E epsilon) :
    horn.boundary_sphere ⊆ horn.carrier := by
  rw [horn.boundary_sphere_eq]
  rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  have ht0 : t = 0 := ht
  subst t
  have hx := (horn.coordinate (q, ⟨0, le_rfl, by norm_num⟩)).property
  rwa [horn.coordinate_eq] at hx

theorem horn_boundary_sphere_not_mem_interior (horn : StrongHorn E epsilon)
    {x : (E.extended.slice T).carrier} (hx : x ∈ horn.boundary_sphere) :
    x ∉ interior horn.carrier := by
  classical
  rw [horn.boundary_sphere_eq] at hx
  rcases hx with ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  have ht0 : t = 0 := ht
  subst t
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ
  let z0 : RoundCylinderSpace := (q, 0)
  have hz0 : z0 ∈ univ ×ˢ Ioo (-horn.collar) 1 :=
    ⟨mem_univ _, neg_lt_zero.mpr horn.collar_pos, by norm_num⟩
  have hf := horn.parameterization_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz0)
  have hf' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3) ∞
      horn.parameterization z0 := by
    simpa only [modelWithCornersSelf_prod] using hf
  have hbij : Function.Bijective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3) horn.parameterization z0) := by
    have hd : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 3)
        horn.parameterization z0 :
        (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) horn.parameterization z0 :=
      congrArg (β := (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (fun I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
          (EuclideanSpace ℝ (Fin 2) × ℝ) =>
            mfderiv I (𝓡 3) horn.parameterization z0) modelWithCornersSelf_prod
    rw [hd]
    exact horn.parameterization_regular z0
      (show (0 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num)
  obtain ⟨U, hU, hinj⟩ := exists_injOn_nhds hf' hbij
  let inv : (E.extended.slice T).carrier → RoundCylinderSpace := fun y =>
    if hy : y ∈ horn.carrier then
      ((horn.coordinate.symm ⟨y, hy⟩).1, ((horn.coordinate.symm ⟨y, hy⟩).2 : ℝ)) else z0
  have hinv : ContinuousOn inv horn.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc := (continuous_fst.comp horn.coordinate.symm.continuous).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp horn.coordinate.symm.continuous))
    convert hc using 1
    ext y <;> simp [inv, y.property]
  have hpinv (y : (E.extended.slice T).carrier) (hy : y ∈ horn.carrier) :
      horn.parameterization (inv y) = y := by
    simp only [inv, dif_pos hy]
    rw [← horn.coordinate_eq]
    exact congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨y, hy⟩)
  have hnonneg (y : (E.extended.slice T).carrier) (hy : y ∈ horn.carrier) :
      0 ≤ (inv y).2 := by
    simp only [inv, dif_pos hy]
    exact (horn.coordinate.symm ⟨y, hy⟩).2.property.1
  have hp0 : horn.parameterization z0 ∈ horn.carrier := by
    have h := (horn.coordinate (q, ⟨0, le_rfl, by norm_num⟩)).property
    rwa [horn.coordinate_eq] at h
  have hi0 : inv (horn.parameterization z0) = z0 := by
    have hc : (⟨horn.parameterization z0, hp0⟩ : horn.carrier) =
        horn.coordinate (q, ⟨0, le_rfl, by norm_num⟩) :=
      Subtype.ext (horn.coordinate_eq (q, ⟨0, le_rfl, by norm_num⟩)).symm
    simp [inv, hp0, hc, z0]
  intro hinterior
  have hnhds := mem_interior_iff_mem_nhds.mp hinterior
  have hi : ContinuousAt inv (horn.parameterization z0) := (hinv _ hp0).continuousAt hnhds
  have hback : ∀ᶠ z in 𝓝 z0, inv (horn.parameterization z) ∈ U :=
    (hi.tendsto.comp hf.continuousAt.tendsto).eventually (hi0.symm ▸ hU)
  have hside : ∀ᶠ z in 𝓝 z0, 0 ≤ z.2 := by
    filter_upwards [hU, hf.continuousAt.tendsto.eventually hnhds, hback] with z hz hzH hzback
    have hzid : inv (horn.parameterization z) = z := hinj hzback hz (hpinv _ hzH)
    rw [← hzid]
    exact hnonneg _ hzH
  have htend : Tendsto (fun s : ℝ => (q, s)) (𝓝 0) (𝓝 z0) :=
    continuousAt_const.prodMk continuousAt_id
  have hhalf : Ici (0 : ℝ) ∈ 𝓝 (0 : ℝ) := htend.eventually hside
  have hzero : (0 : ℝ) ∈ interior (Ici (0 : ℝ)) := mem_interior_iff_mem_nhds.mpr hhalf
  simp only [interior_Ici, mem_Ioi, lt_self_iff_false] at hzero

theorem horn_frontier_carrier_eq_boundary (horn : StrongHorn E epsilon) :
    frontier horn.carrier = horn.boundary_sphere := by
  apply Subset.antisymm (horn_frontier_carrier_subset_boundary horn)
  intro x hx
  exact ⟨subset_closure (horn_boundary_sphere_subset_carrier horn hx),
    horn_boundary_sphere_not_mem_interior horn hx⟩

theorem horn_boundary_subset_closure_interior_part (horn : StrongHorn E epsilon) :
    horn.boundary_sphere ⊆ closure (horn.carrier \ horn.boundary_sphere) := by
  rw [horn_carrier_diff_boundary_eq_image, horn.boundary_sphere_eq]
  rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  have ht0 : t = 0 := ht
  subst t
  apply mem_closure_image
  · exact (horn.parameterization_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ _, neg_lt_zero.mpr horn.collar_pos, by norm_num⟩)).continuousAt
  · rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨mem_univ _, le_rfl, by norm_num⟩

theorem horn_boundary_neck_isSeparating (horn : StrongHorn E epsilon)
    {delta : ℝ} (N : TerminalStrongNeck E delta) (hdelta : delta < 1 / 2)
    (hsphere : N.central_sphere = horn.boundary_sphere) :
    (spatialNeck N hdelta).IsSeparating := by
  let P := spatialNeck N hdelta
  have hpN : N.center ∈ N.carrier := P.central_sphere_subset P.center_on_central_sphere
  have hpB : N.center ∈ horn.boundary_sphere := hsphere ▸ P.center_on_central_sphere
  have hinside := horn_boundary_subset_closure_interior_part horn hpB
  have houtside : N.center ∈ closure horn.carrierᶜ := by
    rw [closure_compl]
    exact horn_boundary_sphere_not_mem_interior horn hpB
  obtain ⟨x, hxN, hxH⟩ := mem_closure_iff.mp hinside N.carrier N.carrier_open hpN
  obtain ⟨y, hyN, hyH⟩ := mem_closure_iff.mp houtside N.carrier N.carrier_open hpN
  refine ⟨P.component_diff_central_sphere_nonempty, ?_⟩
  intro hc
  have hcover : connectedComponent N.center \ N.central_sphere ⊆
      (horn.carrier \ horn.boundary_sphere) ∪ horn.carrierᶜ := by
    intro z hz
    by_cases hzH : z ∈ horn.carrier
    · exact Or.inl ⟨hzH, hsphere ▸ hz.2⟩
    · exact Or.inr hzH
  have hdis : Disjoint (horn.carrier \ horn.boundary_sphere) horn.carrierᶜ :=
    disjoint_left.mpr (fun z hz hz' => hz' hz.1)
  have hxC : x ∈ connectedComponent N.center \ N.central_sphere :=
    ⟨P.carrier_subset_connectedComponent hxN, hsphere.symm ▸ hxH.2⟩
  have hyC : y ∈ connectedComponent N.center \ N.central_sphere :=
    ⟨P.carrier_subset_connectedComponent hyN,
      fun hyS => hyH (horn_boundary_sphere_subset_carrier horn (hsphere ▸ hyS))⟩
  have hsub := hc.isPreconnected.subset_left_of_subset_union
    (horn_isOpen_carrier_diff_boundary horn) (horn_isClosed_carrier horn).isOpen_compl
    hdis hcover ⟨x, hxC, hxH⟩
  exact hyH (hsub hyC).1

end PoincareConjecture.M32
