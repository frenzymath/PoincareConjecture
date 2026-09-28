import PoincareConjecture.Proofs.M36.StandardBalls
import Mathlib.Analysis.Calculus.LocalExtr.Basic










set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.M36

theorem cylindrical_carrier_eq (g₀ : StandardInitialMetric) :
    g₀.cylindrical_end.carrier =
      {x | g₀.cylindrical_end.radius ≤ radialArclength g₀ ‖x‖} := by
  ext x
  rw [g₀.cylindrical_end.carrier_eq]
  simp only [Set.mem_sdiff, Set.mem_univ, true_and, RiemannianMetric.ball,
    Set.mem_ofPred_eq, standard_edist_zero,
    ENNReal.ofReal_lt_ofReal_iff g₀.cylindrical_end.radius_pos, not_lt]

theorem cylindrical_coordinate_mem (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    g₀.cylindrical_end.coordinate z ∈ g₀.cylindrical_end.carrier := by
  rw [← g₀.cylindrical_end.coordinate_image]
  exact ⟨z, ⟨Set.mem_univ _, hz⟩, rfl⟩

theorem cylindrical_coordinate_radial_ge (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    g₀.cylindrical_end.radius ≤
      radialArclength g₀ ‖g₀.cylindrical_end.coordinate z‖ := by
  simpa only [cylindrical_carrier_eq, Set.mem_ofPred_eq] using
    cylindrical_coordinate_mem g₀ z hz

theorem cylindrical_coordinate_contMDiffAt (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : -g₀.cylindrical_end.collar < z.2) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      g₀.cylindrical_end.coordinate z :=
  (g₀.cylindrical_end.coordinate_smooth z ⟨Set.mem_univ _, hz⟩).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨Set.mem_univ _, hz⟩)

theorem cylindrical_carrier_mem_nhds (g₀ : StandardInitialMetric)
    {x : StandardCapSpace}
    (hx : g₀.cylindrical_end.radius < radialArclength g₀ ‖x‖) :
    g₀.cylindrical_end.carrier ∈ nhds x := by
  have hopen : IsOpen {x : StandardCapSpace |
      g₀.cylindrical_end.radius < radialArclength g₀ ‖x‖} :=
    isOpen_lt continuous_const ((radialArclength_contDiff g₀).continuous.comp continuous_norm)
  filter_upwards [hopen.mem_nhds hx] with y hy
  rw [cylindrical_carrier_eq]
  exact hy.le

theorem cylindrical_zero_radial (g₀ : StandardInitialMetric) (theta : UnitTwoSphere) :
    radialArclength g₀ ‖g₀.cylindrical_end.coordinate (theta, 0)‖ =
      g₀.cylindrical_end.radius := by
  apply le_antisymm _ (cylindrical_coordinate_radial_ge g₀ (theta, 0) le_rfl)
  by_contra hle
  have hstrict := lt_of_not_ge hle
  let gamma : ℝ → StandardCapSpace := fun s => g₀.cylindrical_end.coordinate (theta, s)
  let H : ℝ → ℝ := fun s => (g₀.cylindrical_end.inverse (gamma s)).2
  have hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma 0 :=
    (cylindrical_coordinate_contMDiffAt g₀ (theta, 0)
      (neg_lt_zero.mpr g₀.cylindrical_end.collar_pos)).comp 0
        (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hcarrier : g₀.cylindrical_end.carrier ∈ nhds (gamma 0) :=
    cylindrical_carrier_mem_nhds g₀ hstrict
  have hinv : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      g₀.cylindrical_end.inverse (gamma 0) :=
    (g₀.cylindrical_end.inverse_smooth (gamma 0)
      (cylindrical_coordinate_mem g₀ (theta, 0) le_rfl)).contMDiffAt hcarrier
  have hH : DifferentiableAt ℝ H 0 :=
    ((hinv.comp 0 hgamma).snd).contDiffAt.differentiableAt (by simp)
  have hHid : ∀ s ∈ Set.Ici (0 : ℝ), H s = s := by
    intro s hs
    exact congrArg Prod.snd
      (g₀.cylindrical_end.coordinate_left_inverse (x := (theta, s)) ⟨Set.mem_univ _, hs⟩)
  have hmin : IsLocalMin H 0 := by
    change ∀ᶠ s in nhds 0, H 0 ≤ H s
    filter_upwards [hgamma.continuousAt.preimage_mem_nhds hcarrier] with s hs
    rw [hHid 0 Set.self_mem_Ici]
    exact g₀.cylindrical_end.inverse_domain (gamma s) hs
  have hzero : deriv H 0 = 0 := hmin.hasDerivAt_eq_zero hH.hasDerivAt
  have hone : deriv H 0 = 1 :=
    (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hH.hasDerivAt.hasDerivWithinAt
      ((hasDerivWithinAt_id 0 (Set.Ici 0)).congr_of_mem hHid Set.self_mem_Ici)
  exact zero_ne_one (hzero.symm.trans hone)

theorem cylindrical_coordinate_mfderiv_injective (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      g₀.cylindrical_end.coordinate z) := by
  let D : StandardCylinderCoordinates →L[ℝ] StandardCapSpace :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g₀.cylindrical_end.coordinate z
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 2) (𝓡 3) (fun theta : UnitTwoSphere => theta.1) z.1
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩
  have hL : Function.Injective L := by
    convert! injective_mvfderiv_subtypeVal_sphere (n := 2) z.1
  have hnull : ∀ v, D v = 0 → v = 0 := by
    intro v hv
    let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
      g₀.metric.inner (g₀.cylindrical_end.coordinate z)
    have hm := g₀.cylindrical_end.metric_pullback z hz v v
    change B (D v) (D v) =
      2 * (1 - 0) * inner ℝ (L v.1) (L v.1) + v.2 * v.2 at hm
    simp only [hv, map_zero, sub_zero, mul_one,
      real_inner_self_eq_norm_sq] at hm
    have hfirst : L v.1 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by
      nlinarith [sq_nonneg v.2] : ‖L v.1‖ ^ 2 = 0))
    have hsecond : v.2 = 0 := by nlinarith [sq_nonneg ‖L v.1‖]
    exact Prod.ext (hL (hfirst.trans (map_zero L).symm)) hsecond
  change Function.Injective D
  intro v w hvw
  apply sub_eq_zero.mp
  apply hnull
  simp only [map_sub, hvw, sub_self]

theorem cylindrical_coordinate_mfderiv_surjective (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    Function.Surjective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      g₀.cylindrical_end.coordinate z) := by
  let D : StandardCylinderCoordinates →L[ℝ] StandardCapSpace :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g₀.cylindrical_end.coordinate z
  change Function.Surjective D
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := D.toLinearMap)
    (by simp [StandardCylinderCoordinates, StandardCapSpace])).mp
  exact cylindrical_coordinate_mfderiv_injective g₀ z hz

set_option backward.isDefEq.respectTransparency false in
theorem localMin_mfderiv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H N : Type*} [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {f : N → ℝ} {x : N} (hmin : IsLocalMin f x) :
    mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
  have hchart : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    apply IsLocalMin.comp_continuous _ (continuousAt_extChartAt_symm (I := I) x)
    simpa only [extChartAt_to_inv] using hmin
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · rw [hf.mfderiv, I.range_eq_univ, fderivWithin_univ]
    simpa only [writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
      Function.id_comp] using hchart.fderiv_eq_zero
  · exact mfderiv_zero_of_not_mdifferentiableAt hf

theorem radialArclength_norm_fderiv_self (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    fderiv ℝ (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x x =
      radialSpeed g₀ ‖x‖ * ‖x‖ := by
  have hR : DifferentiableAt ℝ
      (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) x :=
    ((radialArclength_contDiff g₀).contDiffAt.comp x
      (contDiffAt_norm ℝ hx)).differentiableAt (by simp)
  have hgamma : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    convert! (hasDerivAt_id (1 : ℝ)).smul_const x using 1
    simp
  have hrad := radial_path_hasDerivAt g₀ hgamma (by simpa using hx)
  have hchain := hR.hasFDerivAt.comp_hasDerivAt_of_eq 1 hgamma (one_smul ℝ x).symm
  have heq := hchain.unique hrad
  simp only [one_smul, real_inner_smul_left, real_inner_self_eq_norm_sq] at heq
  convert! heq using 1
  field_simp

set_option backward.isDefEq.respectTransparency false in
theorem cylindrical_positive_radial (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) :
    g₀.cylindrical_end.radius <
      radialArclength g₀ ‖g₀.cylindrical_end.coordinate z‖ := by
  have hge := cylindrical_coordinate_radial_ge g₀ z hz.le
  apply lt_of_le_of_ne hge
  intro heq
  let R : StandardCapSpace → ℝ := fun x => radialArclength g₀ ‖x‖
  let C := g₀.cylindrical_end.coordinate
  have hboundary : R (C z) = g₀.cylindrical_end.radius := heq.symm
  have hx : C z ≠ 0 := by
    intro hx
    have : (0 : ℝ) = g₀.cylindrical_end.radius := by
      simpa only [R, hx, norm_zero, radialArclength_zero] using hboundary
    linarith [g₀.cylindrical_end.radius_pos]
  have hR : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) R (C z) :=
    (((radialArclength_contDiff g₀).contDiffAt.comp (C z)
      (contDiffAt_norm ℝ hx)).differentiableAt (by simp)).mdifferentiableAt
  have hC : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C z :=
    (cylindrical_coordinate_contMDiffAt g₀ z
      (lt_trans (neg_lt_zero.mpr g₀.cylindrical_end.collar_pos) hz)).mdifferentiableAt
        (by simp)
  have hmin : IsLocalMin (R ∘ C) z := by
    change ∀ᶠ y in nhds z, R (C z) ≤ R (C y)
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with y hy
    rw [hboundary]
    exact cylindrical_coordinate_radial_ge g₀ y hy.le
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (R ∘ C) z = 0 := by
    exact localMin_mfderiv_zero ((𝓡 2).prod 𝓘(ℝ, ℝ)) hmin
  obtain ⟨v, hv⟩ := cylindrical_coordinate_mfderiv_surjective g₀ z hz.le (C z)
  have hval := congrArg (fun L => L v) hd
  rw [mfderiv_comp z hR hC] at hval
  change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) R (C z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C z v) = 0 at hval
  rw [hv] at hval
  change (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) R (C z) : StandardCapSpace →L[ℝ] ℝ)
    (C z) = (0 : ℝ) at hval
  have hzero : fderiv ℝ (fun y : StandardCapSpace => radialArclength g₀ ‖y‖)
      (C z) (C z) = 0 := by
    simpa only [mfderiv_eq_fderiv, R, TangentSpace] using hval
  rw [radialArclength_norm_fderiv_self g₀ hx] at hzero
  exact (mul_pos (radialSpeed_pos g₀ ‖C z‖) (norm_pos_iff.mpr hx)).ne' hzero

theorem cylindrical_boundary_iff (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 ≤ z.2) :
    radialArclength g₀ ‖g₀.cylindrical_end.coordinate z‖ =
        g₀.cylindrical_end.radius ↔ z.2 = 0 := by
  constructor
  · intro heq
    by_contra hne
    exact (cylindrical_positive_radial g₀ z (lt_of_le_of_ne hz (Ne.symm hne))).ne'
      heq
  · intro heq
    simpa only [← heq] using cylindrical_zero_radial g₀ z.1

end PoincareConjecture.M36
