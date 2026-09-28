import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.SmoothRepresentative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateRepresentative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Continuous

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

omit [NeZero n] in
private theorem exists_zero_extended_representative_of_local
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) (v : Lp ℝ 2 g.volumeMeasure)
    (hlocal : ∀ x ∈ closure Ω, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∃ F : M → ℝ, ContinuousOn F V ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F (V ∩ Ω) ∧
        F =ᵐ[g.volumeMeasure.restrict (V ∩ Ω)] (v : M → ℝ) ∧
        ∀ y ∈ V, y ∉ Ω → F y = 0) :
    ∃ F : M → ℝ, Continuous F ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F Ω ∧
      HasCompactSupport F ∧ tsupport F ⊆ closure Ω ∧
      F =ᵐ[g.volumeMeasure.restrict Ω] (v : M → ℝ) ∧
      ∀ x : M, x ∉ Ω → F x = 0 := by
  classical
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  obtain ⟨U, hUs, hUae⟩ := exists_smooth_representative_of_local hΩ v (by
    intro x hx
    obtain ⟨V, hV, hxV, F, -, hFs, hFae, -⟩ := hlocal x (subset_closure hx)
    exact ⟨V ∩ Ω, hV.inter hΩ, ⟨hxV, hx⟩, inter_subset_right, F, hFs, hFae⟩)
  let F : M → ℝ := Ω.indicator U
  have hzero (x : M) (hx : x ∉ Ω) : F x = 0 := indicator_of_notMem hx U
  have hs : tsupport F ⊆ closure Ω := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  have hcontinuous : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ closure Ω
    · obtain ⟨V, hV, hxV, G, hGc, hGs, hGae, hGzero⟩ := hlocal x hx
      have hUG : EqOn U G (V ∩ Ω) :=
        Measure.eqOn_open_of_ae_eq
          (Filter.EventuallyEq.trans
            (ae_restrict_of_ae_restrict_of_subset inter_subset_right hUae) hGae.symm)
          (hV.inter hΩ) (hUs.continuousOn.mono inter_subset_right) hGs.continuousOn
      have hFG : F =ᶠ[𝓝 x] G := by
        filter_upwards [hV.mem_nhds hxV] with y hy
        by_cases hyΩ : y ∈ Ω
        · exact (indicator_of_mem hyΩ U).trans (hUG ⟨hy, hyΩ⟩)
        · rw [hzero y hyΩ, hGzero y hy hyΩ]
      exact (hGc.continuousAt (hV.mem_nhds hxV)).congr_of_eventuallyEq hFG
    · have hFzero : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
        exact hzero y (fun hyΩ => hy (subset_closure hyΩ))
      exact continuousAt_const.congr_of_eventuallyEq hFzero
  refine ⟨F, hcontinuous, hUs.congr ?_,
    hc.of_isClosed_subset isClosed_closure hs, hs, ?_, hzero⟩
  · intro x hx
    exact indicator_of_mem hx U
  · filter_upwards [ae_restrict_mem hΩ.measurableSet, hUae] with x hx hxeq
    exact (indicator_of_mem hx U).trans hxeq

theorem exists_heatPower_continuous_representative (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ∃ F : M → ℝ, Continuous F ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F Ω ∧
      HasCompactSupport F ∧ tsupport F ⊆ closure Ω ∧
      F =ᵐ[g.volumeMeasure.restrict Ω]
        (toL2 D Ω (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
          S.isOpen S.isCompact_closure k t f) : M → ℝ) ∧
      ∀ x : M, x ∉ Ω → F x = 0 := by
  apply exists_zero_extended_representative_of_local S.isOpen S.isCompact_closure
    (toL2 D Ω (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k t f))
  intro x hx
  obtain ⟨e, χ, V, hxT, hxV, hV, -, hVs, he, hei, -, -, -, hone, hflat, hreg⟩ :=
    exists_local_heatPower_continuous D S ⟨x, hx⟩
  obtain ⟨F, hFc, hFs, hae, hzero⟩ := hreg k t ht f
  let H : Set (EuclideanSpace ℝ (Fin n)) := {z | 0 < z 0}
  have hH : IsOpen H := Poincare.Analysis.Sobolev.BoundaryTangential.isOpen_halfSpace
  have hVs' : V ⊆ e.source := subset_closure.trans hVs
  have hVt : e '' V ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hVs' hz)
  have himage : e '' V ∩ Ω = e '' (V ∩ H) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzΩ⟩
      exact ⟨z, ⟨hz, (hflat z (hVs' hz)).mp hzΩ⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzH⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hflat z (hVs' hz)).mpr hzH⟩
  have hcoordinate : F =ᵐ[volume.restrict (V ∩ H)] fun z =>
      toL2 D Ω (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t f) (e z) := by
    filter_upwards [hae, ae_restrict_mem (hV.inter hH).measurableSet] with z hz hzV
    rw [chartPullback_apply e _ (hVs' hzV.1), hone z hzV.1, one_mul] at hz
    exact hz.symm
  refine ⟨e '' V, e.isOpen_image_of_subset_source hV hVs',
    ⟨e.symm x, hxV, e.right_inv hxT⟩, fun y => F (e.symm y),
    hFc.comp_continuousOn (e.symm.continuousOn.mono hVt), ?_, ?_, ?_⟩
  · rw [himage]
    apply hFs.contMDiffOn.comp (hei.mono ((image_mono inter_subset_left).trans hVt))
    rintro y ⟨z, hz, rfl⟩
    simpa only [mem_preimage, e.left_inv (hVs' hz.1)] using hz
  · rw [himage]
    exact g.coordinate_representative_ae e he hei (hV.inter hH)
      (inter_subset_left.trans hVs') hcoordinate
  · rintro y ⟨z, hz, rfl⟩ hyΩ
    dsimp only
    rw [e.left_inv (hVs' hz)]
    apply hzero
    exact not_lt.mp (fun h => hyΩ ((hflat z (hVs' hz)).mpr h))

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
