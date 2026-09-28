import PoincareConjecture.Proofs.M25.AppA_21_Local.Choice
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem CapCertificate.m25_isConnected_carrier (C : CapCertificate g) :
    IsConnected C.carrier := by
  refine ⟨C.core_nonempty.mono C.m25_core_subset_carrier, isPreconnected_of_forall_pair ?_⟩
  intro x hx y hy
  have hle : intrinsicEDist g C.carrier x y ≤ intrinsicDiameter g C.carrier :=
    le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hdist : intrinsicEDist g C.carrier x y < ⊤ :=
    hle.trans_lt (lt_trans C.intrinsic_diameter_bound ENNReal.ofReal_lt_top)
  obtain ⟨L, ⟨γ, hγ, h0, h1, hsub, _⟩, _⟩ := sInf_lt_iff.mp hdist
  refine ⟨γ '' Icc (0 : ℝ) 1, hsub, ?_, ?_,
    isPreconnected_Icc.image γ hγ.continuousOn⟩
  · exact ⟨0, by norm_num, h0⟩
  · exact ⟨1, by norm_num, h1⟩

theorem CapCertificate.m25_closure_core_eq_closed_core (C : CapCertificate g) :
    closure C.core = C.closed_core := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hclosed : IsClosed C.closed_core := C.closed_core_compact.isClosed
  have hboundary : C.boundary_sphere ⊆ closure C.core := by
    intro x hx
    obtain ⟨V, f, hV, hxV, _, hK, hfx, hf, d, _, hd⟩ :=
      C.boundary_local_defining_function x hx
    let c := extChartAt (𝓡 3) x
    let F := f ∘ c.symm
    have hfAt := hf.contMDiffAt (hV.mem_nhds hxV)
    have hfd := hfAt.mdifferentiableAt (by simp)
    have hF : ContDiffAt ℝ ∞ F (c x) := by
      simpa [F, c, mfld_simps, contDiffWithinAt_univ] using (contMDiffAt_iff.mp hfAt).2
    have hdF : fderiv ℝ F (c x) d ≠ 0 := by
      change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x d ≠ 0 at hd
      rw [mfderiv, if_pos hfd] at hd
      rw [modelWithCornersSelf_coe, range_id] at hd
      change fderivWithin ℝ F univ (c x) d ≠ 0 at hd
      simpa only [fderivWithin_univ] using hd
    have hsurj : Function.Surjective (fderiv ℝ F (c x)) := by
      intro r
      refine ⟨(r / fderiv ℝ F (c x) d) • d, ?_⟩
      simp only [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ r hdF
    have hmap : Filter.map F (𝓝 (c x)) = 𝓝 (F (c x)) :=
      (hF.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj
        (LinearMap.range_eq_top.mpr hsurj)
    have hFzero : F (c x) = 0 := by
      simp only [F, Function.comp_apply, c, extChartAt_to_inv, hfx]
    have hnegOpen : IsOpen (V ∩ f ⁻¹' Iio 0) :=
      hf.continuousOn.isOpen_inter_preimage hV isOpen_Iio
    have hnegCore : V ∩ f ⁻¹' Iio 0 ⊆ C.core := by
      rw [C.core_eq_interior_closed_core]
      exact interior_maximal (fun y hy => (hK y hy.1).mpr hy.2.le) hnegOpen
    apply mem_closure_iff.mpr
    intro O hO hxO
    let B := c.symm ⁻¹' (V ∩ O)
    have hB : B ∈ 𝓝 (c x) := by
      apply (continuousAt_extChartAt_symm (I := 𝓡 3) x).preimage_mem_nhds
      simpa only [c, extChartAt_to_inv] using (hV.inter hO).mem_nhds ⟨hxV, hxO⟩
    have himage : F '' B ∈ 𝓝 (0 : ℝ) := by
      have h := Filter.image_mem_map (m := F) hB
      rwa [hmap, hFzero] at h
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
    have hnegative : (-r / 2 : ℝ) ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    obtain ⟨z, hz, hFz⟩ := hball hnegative
    refine ⟨c.symm z, hz.2, hnegCore ⟨hz.1, ?_⟩⟩
    change F z < 0
    rw [hFz]
    linarith
  apply le_antisymm
  · apply closure_minimal _ hclosed
    rw [C.core_eq_interior_closed_core]
    exact interior_subset
  · intro x hx
    by_cases hi : x ∈ interior C.closed_core
    · apply subset_closure
      rwa [C.core_eq_interior_closed_core]
    · apply hboundary
      rw [← C.core_frontier_eq_boundary]
      exact ⟨subset_closure hx, hi⟩

theorem CapCertificate.end_neck_scale_lower (C : CapCertificate g)
    {x : M} {B : ℝ} (hx : x ∈ C.carrier) (hB : C.cap_constant ≤ B) :
    (B * C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ) ≤ C.end_neck.scale := by
  have hcenter : C.end_neck.center ∈ C.carrier :=
    C.end_neck_subset (C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere)
  obtain ⟨b, hb, hratio⟩ := C.scalar_ratio
  have hscalar : C.end_neck.connection.scalarCurvature C.end_neck.center ≤
      B * C.connection.scalarCurvature x := by
    rw [C.end_neck_connection]
    exact (hratio x hx _ hcenter).trans
      (mul_le_mul_of_nonneg_right (hb.le.trans hB) (C.scalar_pos x hx).le)
  rw [C.end_neck.scale_eq_scalar]
  exact Real.rpow_le_rpow_of_nonpos C.end_neck.scalar_center_pos hscalar (by norm_num)

end PoincareConjecture
