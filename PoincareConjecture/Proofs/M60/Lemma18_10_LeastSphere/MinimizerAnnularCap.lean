import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularTopology
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PiecewiseArea
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.MeasureTheory.Function.Jacobian










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology Manifold ContDiff InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

local instance : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩



def suAnnularReflection (p : UnitTwoSphere) : UnitTwoSphere :=
  ⟨(ℝ ∙ m60SpherePole.val)ᗮ.reflection p.val, by
    simpa only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] using p.property⟩



theorem suAnnularReflection_smooth :
    ContMDiff (𝓡 2) (𝓡 2) ∞ suAnnularReflection := by
  exact (((ℝ ∙ m60SpherePole.val)ᗮ.reflection.toContinuousLinearMap.contDiff).contMDiff.comp
    contMDiff_coe_sphere).codRestrict_sphere _



def suAnnularCap (R : ℝ) (z : LoopPlane) : UnitTwoSphere :=
  suAnnularReflection (m60SphereParameter ((4 / R ^ 2) • z))



theorem suAnnularCap_smooth (R : ℝ) : ContMDiff (𝓡 2) (𝓡 2) ∞ (suAnnularCap R) :=
  suAnnularReflection_smooth.comp (m60SphereParameter_contMDiff.comp
    (((4 / R ^ 2) • ContinuousLinearMap.id ℝ LoopPlane).contDiff.contMDiff))




theorem suAnnularReflection_parameter {z : LoopPlane} (hz : z ≠ 0) :
    suAnnularReflection (m60SphereParameter z) =
      m60SphereParameter ((4 / ‖z‖ ^ 2) • z) := by
  let U : (ℝ ∙ m60SpherePole.val)ᗮ ≃ₗᵢ[ℝ] LoopPlane :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2
      (ne_zero_of_mem_unit_sphere m60SpherePole)).repr
  let L := (ℝ ∙ m60SpherePole.val)ᗮ.reflection
  have hparam (x : LoopPlane) : (m60SphereParameter x).val =
      (4 / (‖x‖ ^ 2 + 4)) • (U.symm x : LoopAmbient) +
        ((‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4)) • m60SpherePole.val := by
    change ((stereographic' 2 m60SpherePole).symm x : LoopAmbient) = _
    rw [stereographic'_symm_apply]
    change (‖(U.symm x : LoopAmbient)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
      (U.symm x : LoopAmbient) + (‖(U.symm x : LoopAmbient)‖ ^ 2 + 4)⁻¹ •
        (‖(U.symm x : LoopAmbient)‖ ^ 2 - 4) • m60SpherePole.val = _
    have hn : ‖(U.symm x : LoopAmbient)‖ = ‖x‖ := U.symm.norm_map x
    rw [hn]
    simp only [smul_smul, div_eq_mul_inv]
    congr 2 <;> ring
  have hplane (x : LoopPlane) : L (U.symm x : LoopAmbient) = (U.symm x : LoopAmbient) :=
    Submodule.reflection_mem_subspace_eq_self (U.symm x).property
  have hpole : L m60SpherePole.val = -m60SpherePole.val :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg _
  have hn : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  let s := 4 / ‖z‖ ^ 2
  have hs : 0 < s := div_pos (by norm_num) hn
  have hnorm : ‖s • z‖ ^ 2 = s ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hs.le, mul_pow]
  have hfirst : 4 / (‖z‖ ^ 2 + 4) = 4 / (s ^ 2 * ‖z‖ ^ 2 + 4) * s := by
    dsimp only [s]
    field_simp
    ring
  have hlast : -((‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4)) =
      (s ^ 2 * ‖z‖ ^ 2 - 4) / (s ^ 2 * ‖z‖ ^ 2 + 4) := by
    dsimp only [s]
    field_simp
    ring
  apply Subtype.ext
  change L (m60SphereParameter z).val = (m60SphereParameter (s • z)).val
  rw [hparam, map_add, map_smul, map_smul, hplane, hpole, hparam,
    hnorm, map_smul, Submodule.coe_smul_of_tower, smul_smul]
  rw [smul_neg, ← neg_smul, hfirst, hlast]



theorem suAnnularCap_eq_inversion {R : ℝ} (hR : 0 < R)
    {z : LoopPlane} (hz : z ≠ 0) :
    suAnnularCap R z = m60SphereParameter ((R ^ 2 / ‖z‖ ^ 2) • z) := by
  have hs : 0 < 4 / R ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hR)
  rw [suAnnularCap, suAnnularReflection_parameter (smul_ne_zero hs.ne' hz),
    norm_smul, Real.norm_of_nonneg hs.le, smul_smul]
  congr 2
  field_simp



theorem suAnnularCap_boundary {R : ℝ} (hR : 0 < R)
    {z : LoopPlane} (hz : ‖z‖ = R) : suAnnularCap R z = m60SphereParameter z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne hR.ne')
  rw [suAnnularCap_eq_inversion hR hz0, hz, div_self (pow_ne_zero 2 hR.ne'), one_smul]



theorem suAnnularCap_relative_homotopy
    {Y : Type*} [TopologicalSpace Y] (v : C(UnitTwoSphere, Y)) (hv : v.Nullhomotopic)
    {R : ℝ} (hR : 0 < R) :
    (v.comp ⟨fun z : closedBall (0 : LoopPlane) R => m60SphereParameter z,
      m60SphereParameter_contMDiff.continuous.comp continuous_subtype_val⟩).HomotopicRel
      (v.comp ⟨fun z : closedBall (0 : LoopPlane) R => suAnnularCap R z,
        (suAnnularCap_smooth R).continuous.comp continuous_subtype_val⟩)
      {z : closedBall (0 : LoopPlane) R | ‖z.val‖ = R} := by
  apply suNullSphere_relative_caps v hv
  intro z hz
  exact (suAnnularCap_boundary hR hz).symm

section Area

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open scoped Bundle in



theorem suAreaDensity_comp_plane (g : RiemannianMetric n M)
    {f : LoopPlane → M} {k : LoopPlane → LoopPlane} {z : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (k z)) (hk : DifferentiableAt ℝ k z) :
    m60AreaDensity g (f ∘ k) z =
      |(fderiv ℝ k z).det| * m60AreaDensity g f (k z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let A := fderiv ℝ k z
  let D := mfderiv (𝓡 2) (𝓡 n) f (k z)
  let u := D (e 0)
  let v := D (e 1)
  have harea (F : LoopPlane → M) (x : LoopPlane) :
      m60AreaDensity g F x = Proofs.M58.twoVectorArea
        (mfderiv (𝓡 2) (𝓡 n) F x (e 0)) (mfderiv (𝓡 2) (𝓡 n) F x (e 1)) := by
    let u' := mfderiv (𝓡 2) (𝓡 n) F x (e 0)
    let v' := mfderiv (𝓡 2) (𝓡 n) F x (e 1)
    unfold m60AreaDensity m60AreaGram Proofs.M58.twoVectorArea
    dsimp only
    erw [Matrix.det_fin_two]
    change Real.sqrt (max 0 (inner ℝ u' u' * inner ℝ v' v' -
      inner ℝ u' v' * inner ℝ v' u')) = _
    rw [real_inner_comm v' u', pow_two]
  have hrep (w : LoopPlane) : D w = w 0 • u + w 1 • v := by
    have hw : w = w 0 • e 0 + w 1 • e 1 := by
      simpa only [e, Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using (e.sum_repr w).symm
    calc
      D w = D (w 0 • e 0 + w 1 • e 1) := congrArg D hw
      _ = _ := by rw [map_add, map_smul, map_smul]
  have hd : A.det = (A (e 0)) 0 * (A (e 1)) 1 - (A (e 0)) 1 * (A (e 1)) 0 := by
    change LinearMap.det A.toLinearMap = _
    rw [← LinearMap.det_toMatrix e.toBasis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, e, EuclideanSpace.basisFun_repr, ContinuousLinearMap.coe_coe]
    ring
  rw [harea, harea, mfderiv_comp z hf hk.hasFDerivAt.hasMFDerivAt.mdifferentiableAt,
    mfderiv_eq_fderiv]
  change Proofs.M58.twoVectorArea (D (A (e 0))) (D (A (e 1))) = _
  rw [hrep, hrep, Proofs.M58.twoVectorArea_change, hd]

private theorem annular_inversion_image {R : ℝ} (hR : 0 < R) :
    EuclideanGeometry.inversion (0 : LoopPlane) R '' (ball 0 R \ {0}) =
      (closedBall (0 : LoopPlane) R)ᶜ := by
  have hnorm (z : LoopPlane) : ‖EuclideanGeometry.inversion 0 R z‖ = R ^ 2 / ‖z‖ := by
    simpa only [dist_zero_right] using EuclideanGeometry.dist_inversion_center 0 z R
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw.2
    have hwr : ‖w‖ < R := mem_ball_zero_iff.mp hw.1
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le, hnorm]
    exact (lt_div_iff₀ hw0).mpr (by nlinarith only [hwr, hR])
  · intro hz
    have hzr : R < ‖z‖ := by simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hR.trans hzr)
    refine ⟨EuclideanGeometry.inversion 0 R z, ⟨?_, ?_⟩,
      EuclideanGeometry.inversion_inversion 0 hR.ne' z⟩
    · rw [mem_ball_zero_iff, hnorm]
      exact (div_lt_iff₀ (hR.trans hzr)).mpr (by nlinarith only [hzr, hR])
    · exact fun h => hz0 ((EuclideanGeometry.inversion_eq_center hR.ne').mp h)




theorem suAnnularCap_area (g : RiemannianMetric n M)
    {v : UnitTwoSphere → M} (hv : ContMDiff (𝓡 2) (𝓡 n) 1 v)
    {R : ℝ} (hR : 0 < R) :
    IntegrableOn (m60AreaDensity g (v ∘ suAnnularCap R)) (ball (0 : LoopPlane) R) ∧
      IntegrableOn (m60SphereAreaDensity g v) (closedBall (0 : LoopPlane) R)ᶜ ∧
      (∫ z in ball (0 : LoopPlane) R, m60AreaDensity g (v ∘ suAnnularCap R) z) =
        ∫ z in (closedBall (0 : LoopPlane) R)ᶜ, m60SphereAreaDensity g v z := by
  let k := EuclideanGeometry.inversion (0 : LoopPlane) R
  let F := v ∘ m60SphereParameter
  let S := ball (0 : LoopPlane) R \ {0}
  have hS : MeasurableSet S := measurableSet_ball.diff (measurableSet_singleton _)
  have hk {z : LoopPlane} (hz : z ≠ 0) : DifferentiableAt ℝ k z :=
    (EuclideanGeometry.hasFDerivAt_inversion hz).differentiableAt
  have hF : ContMDiff (𝓡 2) (𝓡 n) 1 F :=
    hv.comp (m60SphereParameter_contMDiff.of_le (by simp))
  have hc : ContMDiff (𝓡 2) (𝓡 n) 1 (v ∘ suAnnularCap R) :=
    hv.comp ((suAnnularCap_smooth R).of_le (by simp))
  have hint : IntegrableOn (m60AreaDensity g (v ∘ suAnnularCap R)) (ball 0 R) :=
    ((m60AreaDensity_continuous g hc).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) R)).mono_set ball_subset_closedBall
  have heq (z : LoopPlane) (hz : z ∈ S) :
      m60AreaDensity g (v ∘ suAnnularCap R) z =
        |(fderiv ℝ k z).det| * m60AreaDensity g F (k z) := by
    have hgerm : (v ∘ suAnnularCap R) =ᶠ[𝓝 z] F ∘ k := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz.2] with y hy
      dsimp only [Function.comp_apply, F]
      rw [suAnnularCap_eq_inversion hR hy]
      congr 2
      simp only [k, EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub,
        sub_zero, vadd_eq_add, add_zero, div_pow]
    rw [m60AreaDensity_congr_of_eventuallyEq g hgerm]
    exact suAreaDensity_comp_plane g (hF.mdifferentiable one_ne_zero _) (hk hz.2)
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z hz => (hk hz.2).hasFDerivAt.hasFDerivWithinAt)
    (EuclideanGeometry.inversion_injective 0 hR.ne').injOn (m60AreaDensity g F)
  have hnull : S =ᵐ[volume] ball (0 : LoopPlane) R :=
    sdiff_null_ae_eq_self (measure_singleton (0 : LoopPlane))
  refine ⟨hint, (m60SphereAreaDensity_integrable g v hv).integrableOn, ?_⟩
  rw [← setIntegral_congr_set hnull]
  calc
    _ = ∫ z in S, |(fderiv ℝ k z).det| • m60AreaDensity g F (k z) :=
      setIntegral_congr_fun hS (fun z hz => by simpa only [smul_eq_mul] using heq z hz)
    _ = ∫ z in k '' S, m60AreaDensity g F z := hj.symm
    _ = _ := by rw [annular_inversion_image hR]; rfl




theorem suSphereArea_chart (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (c : UnitTwoSphere) :
    Integrable (m60AreaDensity g (f ∘ (chartAt LoopPlane c).symm)) volume ∧
      (∫ z, m60AreaDensity g (f ∘ (chartAt LoopPlane c).symm) z) = m60SphereArea g f := by
  let a := -m60SpherePole
  let e := chartAt LoopPlane c
  let e₀ := chartAt LoopPlane a
  let F := f ∘ e.symm
  let F₀ := f ∘ e₀.symm
  let k : LoopPlane → LoopPlane := e ∘ e₀.symm
  let S := e₀.symm ⁻¹' e.source
  let T := e.symm ⁻¹' e₀.source
  have htarget (p : UnitTwoSphere) (z : LoopPlane) : z ∈ (chartAt LoopPlane p).target := by
    rw [suSphereChart_target]
    exact mem_univ z
  have hsource (p : UnitTwoSphere) : (chartAt LoopPlane p).source = {-p}ᶜ := by
    change (stereographic' 2 (-p)).source = _
    simp
  have hinv (p : UnitTwoSphere) : Function.Injective (chartAt LoopPlane p).symm := by
    intro x y hxy
    have hh := congrArg (chartAt LoopPlane p) hxy
    simpa only [(chartAt LoopPlane p).right_inv (htarget p x),
      (chartAt LoopPlane p).right_inv (htarget p y)] using hh
  have hnull (p q : UnitTwoSphere) :
      (chartAt LoopPlane p).symm ⁻¹' (chartAt LoopPlane q).source =ᵐ[volume] univ := by
    apply ae_eq_univ.mpr
    rw [hsource, preimage_compl, compl_compl]
    exact ((finite_singleton (-q)).preimage (hinv p).injOn).measure_zero volume
  have hSnull : S =ᵐ[volume] univ := hnull a c
  have hTnull : T =ᵐ[volume] univ := hnull c a
  have hSopen : IsOpen S := e.open_source.preimage (suSphereChart_smooth a).continuous
  have himage : k '' S = T := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change e.symm (e (e₀.symm w)) ∈ e₀.source
      rw [e.left_inv hw]
      exact e₀.map_target (htarget a w)
    · intro hz
      refine ⟨e₀ (e.symm z), ?_, ?_⟩
      · change e₀.symm (e₀ (e.symm z)) ∈ e.source
        rw [e₀.left_inv hz]
        exact e.map_target (htarget c z)
      · change e (e₀.symm (e₀ (e.symm z))) = z
        rw [e₀.left_inv hz, e.right_inv (htarget c z)]
  have hkinj : InjOn k S := fun _ hx _ hy h => (hinv a) (e.injOn hx hy h)
  have hk (z : LoopPlane) (hz : z ∈ S) : DifferentiableAt ℝ k z := by
    have hech : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source := contMDiffOn_chart
    have he : ContMDiffAt (𝓡 2) (𝓡 2) ∞ e (e₀.symm z) :=
      hech.contMDiffAt (e.open_source.mem_nhds hz)
    exact (contMDiffAt_iff_contDiffAt.mp
      (he.comp z ((suSphereChart_smooth a) z))).differentiableAt (by simp)
  have hF : ContMDiff (𝓡 2) (𝓡 n) 1 F := hf.comp ((suSphereChart_smooth c).of_le (by simp))
  have heq (z : LoopPlane) (hz : z ∈ S) :
      m60AreaDensity g F₀ z = |(fderiv ℝ k z).det| • m60AreaDensity g F (k z) := by
    have hgerm : F₀ =ᶠ[𝓝 z] F ∘ k := by
      filter_upwards [hSopen.mem_nhds hz] with y hy
      change f (e₀.symm y) = f (e.symm (e (e₀.symm y)))
      rw [e.left_inv hy]
    rw [m60AreaDensity_congr_of_eventuallyEq g hgerm]
    exact suAreaDensity_comp_plane g (hF.mdifferentiable one_ne_zero _) (hk z hz)
  have hF₀eq : m60AreaDensity g F₀ = m60SphereAreaDensity g f := by
    funext z
    change m60AreaDensity g (f ∘ (chartAt LoopPlane (-m60SpherePole)).symm) z =
      m60AreaDensity g (f ∘ m60SphereChart.symm) z
    rw [m60SphereChart_eq_chartAt]
  have hF₀int : Integrable (m60AreaDensity g F₀) volume := by
    rw [hF₀eq]
    exact m60SphereAreaDensity_integrable g f hf
  have hweighted : IntegrableOn
      (fun z => |(fderiv ℝ k z).det| • m60AreaDensity g F (k z)) S :=
    hF₀int.integrableOn.congr_fun (fun z hz => heq z hz) hSopen.measurableSet
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hSopen.measurableSet (fun z hz => (hk z hz).hasFDerivAt.hasFDerivWithinAt)
    hkinj (m60AreaDensity g F)).mpr hweighted
  rw [himage] at hint
  refine ⟨integrableOn_univ.mp (hint.congr_set_ae hTnull.symm), ?_⟩
  calc
    _ = ∫ z in k '' S, m60AreaDensity g F z := by
      rw [himage, setIntegral_congr_set hTnull, setIntegral_univ]
    _ = ∫ z in S, |(fderiv ℝ k z).det| • m60AreaDensity g F (k z) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hSopen.measurableSet
        (fun z hz => (hk z hz).hasFDerivAt.hasFDerivWithinAt) hkinj _
    _ = ∫ z in S, m60AreaDensity g F₀ z :=
      setIntegral_congr_fun hSopen.measurableSet (fun z hz => (heq z hz).symm)
    _ = _ := by rw [setIntegral_congr_set hSnull, setIntegral_univ, hF₀eq]; rfl

end Area

end PoincareConjecture.M60
