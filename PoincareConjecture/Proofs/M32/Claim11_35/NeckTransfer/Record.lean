import PoincareConjecture.Proofs.M32.Claim11_35.NeckTransfer.PartialSource
import PoincareConjecture.Proofs.M32.Cor11_36.Restriction
import PoincareConjecture.Proofs.M32.Claim11_35.FiniteSlabs
import PoincareConjecture.Proofs.M32.Claim11_34.ZeroSlicePoint
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

private noncomputable def neckCylinderScaleCast
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (d : GeneralizedFlowCylinder F C a q I U) (h : q = q') :
    GeneralizedFlowCylinder F C a q' I U := h ▸ d

private theorem neckCylinderScaleCast_pointMap
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (d : GeneralizedFlowCylinder F C a q I U) (h : q = q')
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) :
    (neckCylinderScaleCast d h).pointMap s hs x = d.pointMap s hs x := by
  cases h
  rfl

private theorem neckCylinderScaleCast_pullback
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {a q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (d : GeneralizedFlowCylinder F C a q I U) (h : q = q')
    (Φ : RoundCylinderSpace → C.carrier) :
    generalizedCylinderPullback (neckCylinderScaleCast d h) Φ =
      generalizedCylinderPullback d Φ := by
  cases h
  rfl

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem blowup_exists_strongNeck_of_cylinderFamilyClose
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    (Φ : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace G.limit.sliceCarrier.carrier ∞)
    (q : UnitTwoSphere) (hcenter : Φ (q, 0) = G.limit.base)
    {delta : ℝ} (hdelta : 0 < delta) (k : ℕ)
    (hspace : Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) ⊆ G.exhaustion.space k)
    (hI : Ioc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0)
    (hclose : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback (G.embedding k) Φ)) :
    ∃ N : GeneralizedStrongNeck (S.flow (G.subsequence k))
        (S.base (G.subsequence k)).1 delta,
      N.center = (S.base (G.subsequence k)).2 ∧
      N.scale = S.scale (G.subsequence k) ^ (-1 / 2 : ℝ) ∧
      N.carrier = blowup_zeroSliceEmbedding G k ''
        (Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹)) ∧
      N.coordinate_map = blowup_zeroSliceEmbedding G k ∘ Φ ∧
      N.coordinate_inverse = Φ.symm ∘ (blowup_zeroSliceEmbedding G k).symm ∧
      N.central_sphere = (blowup_zeroSliceEmbedding G k ∘ Φ) ''
        (univ ×ˢ ({0} : Set ℝ)) ∧
      ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0) y, y ∈ N.carrier →
        N.time_cylinder.pointMap s hs y =
          (G.embedding k).pointMap s (hI hs) ((blowup_zeroSliceEmbedding G k).symm y) := by
  let E := blowup_zeroSliceEmbedding G k
  let V := Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹)
  let W := E '' V
  have hV : IsOpen V := Φ.toHomeomorph.isOpenMap _ (isOpen_univ.prod isOpen_Ioo)
  have hVE : V ⊆ E.source := by
    simpa only [E, blowup_zeroSliceEmbedding_source] using hspace
  have hW : IsOpen W := E.isOpen_image_of_subset_source hV hVE
  have hWE : W ⊆ E.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact E.map_source (hVE hx)
  let e : OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier := {
    toFun := E
    invFun := E.symm
    source := V
    target := W
    map_source' := fun x hx => mem_image_of_mem E hx
    map_target' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [E.left_inv (hVE hx)]
      exact hx
    left_inv' := fun x hx => E.left_inv (hVE hx)
    right_inv' := fun x hx => E.right_inv (hWE hx)
    open_source := hV
    open_target := hW
    continuousOn_toFun := E.continuousOn_toFun.mono hVE
    continuousOn_invFun := E.continuousOn_invFun.mono hWE }
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e V :=
    (blowup_zeroSliceEmbedding_smooth G k).mono hspace
  have hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm W :=
    (blowup_zeroSliceEmbedding_symm_smooth G k).mono hWE
  have hΦV : MapsTo Φ (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) V :=
    fun x hx => mem_image_of_mem Φ hx
  let coordinate : RoundCylinderSpace →
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier := E ∘ Φ
  let inverse := Φ.symm ∘ E.symm
  have hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) :=
    he.comp Φ.contMDiff.contMDiffOn hΦV
  have hinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse W :=
    Φ.symm.contMDiff.comp_contMDiffOn hei
  let f : OpenPartialHomeomorph RoundCylinderSpace
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier := {
    toFun := coordinate
    invFun := inverse
    source := univ ×ˢ Ioo (-delta⁻¹) delta⁻¹
    target := W
    map_source' := fun z hz => mem_image_of_mem E (hΦV hz)
    map_target' := by
      rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      change Φ.symm (E.symm (E (Φ z))) ∈ univ ×ˢ Ioo (-delta⁻¹) delta⁻¹
      rw [E.left_inv (hVE (hΦV hz)), Φ.symm_apply_apply]
      exact hz
    left_inv' := by
      intro z hz
      change Φ.symm (E.symm (E (Φ z))) = z
      rw [E.left_inv (hVE (hΦV hz)), Φ.symm_apply_apply]
    right_inv' := by
      intro x hx
      change E (Φ (Φ.symm (E.symm x))) = x
      rw [Φ.apply_symm_apply, E.right_inv (hWE hx)]
    open_source := isOpen_univ.prod isOpen_Ioo
    open_target := hW
    continuousOn_toFun := hcoordinate.continuousOn
    continuousOn_invFun := hinverse.continuousOn }
  let d := restrictCylinderTime (restrictCylinderSpace (G.embedding k) hspace) hI
  let c := rebasePartialCylinderSource d e.symm (by rfl) hei he
  have hpoint (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) (y) :
      c.pointMap s hs y = (G.embedding k).pointMap s (hI hs) (E.symm y) := rfl
  have hzero (h : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0) (y) (hy : y ∈ W) :
      c.pointMap 0 h y =
        (⟨(S.base (G.subsequence k)).1, y⟩ : (S.flow (G.subsequence k)).point) := by
    rw [hpoint, blowup_zeroSliceEmbedding_pointMap]
    change (⟨(S.base (G.subsequence k)).1, E (E.symm y)⟩ :
      (S.flow (G.subsequence k)).point) = _
    rw [E.right_inv (hWE hy)]
  have hcomparison : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback c coordinate) := by
    apply roundCylinderFamilyClose_congr_axial
      (B' := generalizedCylinderPullback (G.embedding k) Φ) ?_ hclose
    intro s hs z hz v w
    have hz' : z ∈ univ ×ˢ Ioo (-delta⁻¹) delta⁻¹ := ⟨mem_univ _, hz⟩
    have hΦz : Φ z ∈ e.source := hΦV hz'
    have hcz : coordinate z ∈ e.target := e.map_source hΦz
    have hd := (hcoordinate.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz')).mdifferentiableAt (by simp)
    have hi := (hei.contMDiffAt (hW.mem_nhds hcz)).mdifferentiableAt (by simp)
    have heq : e.symm ∘ coordinate =ᶠ[𝓝 z] Φ := by
      filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz'] with y hy
      exact e.left_inv (hΦV hy)
    have hderiv : (mfderiv (𝓡 3) (𝓡 3) e.symm (coordinate z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z := by
      rw [← mfderiv_comp z hi hd]
      exact heq.mfderiv_eq
    have hderiv_apply (v : RoundCylinderTangent z) :
        mfderiv (𝓡 3) (𝓡 3) e.symm (coordinate z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v) =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v :=
      congrArg (fun A => A v) hderiv
    simp only [generalizedCylinderPullback, dif_pos hs, dif_pos (hI hs)]
    change (rebasePartialCylinderSource d e.symm _ _ _).pullbackInner s hs
      (coordinate z) _ _ = _
    rw [rebasePartialCylinderSource_pullbackInner d e.symm _ _ _ hV s hs
      (coordinate z) hcz, hderiv_apply v, hderiv_apply w]
    change d.pullbackInner s hs (e.symm (e (Φ z))) _ _ = _
    rw [e.left_inv hΦz]
    rfl
  let scale := S.scale (G.subsequence k) ^ (-1 / 2 : ℝ)
  have hQ : 0 < S.scale (G.subsequence k) := S.base_scalar_pos (G.subsequence k)
  have hscale_pos : 0 < scale := Real.rpow_pos_of_pos hQ _
  have hscale : scale⁻¹ ^ 2 = S.scale (G.subsequence k) := by
    have hsqrt : scale = (Real.sqrt (S.scale (G.subsequence k)))⁻¹ := by
      dsimp only [scale]
      rw [neg_div, Real.rpow_neg hQ.le, Real.sqrt_eq_rpow]
    rw [hsqrt, inv_inv, Real.sq_sqrt hQ.le]
  let c' := neckCylinderScaleCast c hscale.symm
  have hcomparison' : RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback c' coordinate) := by
    rw [show generalizedCylinderPullback c' coordinate =
      generalizedCylinderPullback c coordinate from
      neckCylinderScaleCast_pullback c hscale.symm coordinate]
    exact hcomparison
  have hsphere : coordinate '' (univ ×ˢ ({0} : Set ℝ)) ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    apply f.map_source
    have hpos := inv_pos.mpr hdelta
    exact ⟨mem_univ _, by
      simpa only [mem_singleton_iff.mp hz.2] using
        (show (0 : ℝ) ∈ Ioo (-delta⁻¹) delta⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩
  let N : GeneralizedStrongNeck (S.flow (G.subsequence k))
      (S.base (G.subsequence k)).1 delta := {
    epsilon_pos := hdelta
    center := (S.base (G.subsequence k)).2
    scalar_center_pos := hQ
    scale := scale
    scale_pos := hscale_pos
    scale_scalar := rfl
    carrier := W
    carrier_open := hW
    coordinate := neckDomainCoordinates f rfl
    coordinate_map := coordinate
    coordinate_map_eq := neckDomainCoordinates_coe f rfl
    coordinate_map_smooth := hcoordinate
    coordinate_inverse := inverse
    coordinate_inverse_mem := fun _ hx => (neckDomainCoordinates_inverse_mem f rfl hx).2
    coordinate_inverse_left := neckDomainCoordinates_inverse_left f rfl
    coordinate_inverse_right := fun x hx => f.right_inv hx
    coordinate_inverse_smooth := hinverse
    central_sphere := coordinate '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := by
      refine ⟨(q, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      change E (Φ (q, 0)) = (S.base (G.subsequence k)).2
      rw [hcenter]
      exact blowup_zeroSliceEmbedding_base G k
    central_sphere_subset := hsphere
    time_cylinder := c'
    cylinder_identity := fun h x hx =>
      (neckCylinderScaleCast_pointMap c hscale.symm 0 h x).trans (hzero h x hx)
    metric_comparison := hcomparison' }
  refine ⟨N, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro s hs y _hy
  exact (neckCylinderScaleCast_pointMap c hscale.symm s hs y).trans (hpoint s hs y)

end PoincareConjecture.M32
