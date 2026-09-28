import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.AdjacentParameters
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Cancellation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in

theorem chartTriangle_vertical_velocity
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {t : ℝ} (ht : (0, t) ∈ e.target) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun s : ℝ => e.symm (0, s)) t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => e.symm (0, s)) t 1 =
        mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) (e.symm (0, t)) := by
  have h := LeviCivitaData.mfderiv_chart_line e he hei (0, 0) (0, 1)
    (t := t) (by simpa using ht)
  have hcurve : (fun s : ℝ => e.symm ((0, 0) + s • (0, 1))) =
      fun s : ℝ => e.symm (0, s) := by
    funext s
    simp
  have hpoint := congrFun hcurve t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve, hpoint] at h
  exact h



theorem integral_chartTriangle_shared_side_pair_eq_zero
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (e f : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ f f.source)
    (hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f.symm f.target)
    (Q : RiemannianMetric.AlignedChartFrame g e) (R : RiemannianMetric.AlignedChartFrame g f)
    (het : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ e.target)
    (hft : ∀ s ∈ Icc (0 : ℝ) 1, (0, s) ∈ f.target)
    (himage : (fun s : ℝ => f.symm (0, s)) '' Icc (0 : ℝ) 1 =
      (fun s : ℝ => e.symm (0, s)) '' Icc (0 : ℝ) 1)
    (hdisjoint : Disjoint
      (e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      (f.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})) :
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let Z := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) f (fun _ => (0, 1))
    let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
    let W := fun x => (Real.sqrt (g.inner x (Z x) (Z x)))⁻¹ • Z x
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second W Z (f.symm (0, t))) +
      (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second T Y (e.symm (0, t))) = 0 := by
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  let Z := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) f (fun _ => (0, 1))
  let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
  let W := fun x => (Real.sqrt (g.inner x (Z x) (Z x)))⁻¹ • Z x
  let γ := fun t : ℝ => e.symm (0, t)
  let η := fun t : ℝ => f.symm (0, t)
  let φ := fun t : ℝ => (e (f.symm (0, t))).2
  obtain ⟨hsmooth, hbij, _, hpoint⟩ := chartTriangle_side_parameter e f he hfi het hft himage
  obtain ⟨δ, _, hsign, hends⟩ :=
    exists_chartTriangle_side_orientation g e f he hei hf hfi Q R het hft himage hdisjoint
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ (φ t) = η t := hpoint t ht
  have hT : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% T) e.source :=
    (LeviCivitaData.normalized_chartField_properties g e he hei
      (v := (0, 1)) (by norm_num)).1
  have hW : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% W) f.source :=
    (LeviCivitaData.normalized_chartField_properties g f hf hfi
      (v := (0, 1)) (by norm_num)).1
  have hY : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Y) e.source :=
    fun x hx => (LeviCivitaData.contMDiffAt_chartField e he hei hx (0, 1)).contMDiffWithinAt
  have himg : φ '' uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le zero_le_one]
    exact hbij.image_eq
  have hφ (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : HasDerivAt φ (deriv φ t) t := by
    rw [uIcc_of_le zero_le_one] at ht
    exact ((hsmooth t ht).differentiableAt (by simp)).hasDerivAt
  have hφ' : ContinuousOn (deriv φ) (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact ((hsmooth t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hγ (s : ℝ) (hs : s ∈ φ '' uIcc (0 : ℝ) 1) :
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ s := by
    rw [himg] at hs
    exact (chartTriangle_vertical_velocity e he hei (het s hs)).1.mdifferentiableAt (by simp)
  have hγU : MapsTo γ (φ '' uIcc (0 : ℝ) 1) e.source := by
    intro s hs
    rw [himg] at hs
    exact e.map_target (het s hs)
  have hW' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ (φ t)) := by
    rw [hp t (Ioo_subset_Icc_self ht)]
    exact (hW.contMDiffAt (f.open_source.mem_nhds
      (f.map_target (hft t (Ioo_subset_Icc_self ht))))).mdifferentiableAt (by simp)
  have hv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      Y (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ (φ t) 1 :=
    (chartTriangle_vertical_velocity e he hei
      (het _ (hbij.mapsTo (Ioo_subset_Icc_self ht)))).2.symm
  have hz (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      Z (γ (φ t)) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ ∘ φ) t 1 := by
    have hlocal : γ ∘ φ =ᶠ[𝓝 t] η :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
        (fun s hs => hp s (Ioo_subset_Icc_self hs))
    dsimp only [TangentSpace] at hlocal ⊢
    rw [hlocal.mfderiv_eq, hp t (Ioo_subset_Icc_self ht)]
    exact (chartTriangle_vertical_velocity f hf hfi (hft t (Ioo_subset_Icc_self ht))).2.symm
  have hregular (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Z (γ (φ t)) ≠ 0 := by
    dsimp only [TangentSpace]
    rw [hp t (Ioo_subset_Icc_self ht)]
    exact LeviCivitaData.chartField_ne_zero f hf hfi (v := (0, 1)) (by norm_num)
      (f.map_target (hft t (Ioo_subset_Icc_self ht)))
  have hdet (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      g.frameOrientation (γ (φ t)) (Q.first (γ (φ t))) (Q.second (γ (φ t)))
        (R.first (γ (φ t))) (R.second (γ (φ t))) = δ := by
    rw [hp t (Ioo_subset_Icc_self ht)]
    exact hsign t (Ioo_subset_Icc_self ht)
  have hcancel := D.integral_normalized_surfaceTurningForm_pair_eq_zero
    e.open_source Q.smooth_first Q.smooth_second hT hY Q.unit_first Q.unit_second Q.orthogonal
    zero_le_one hφ hφ' hγ hγU hW' hv hz hdet hregular
    (fun _ _ => rfl) (fun _ _ => rfl) hends
  have heq : (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second W Z (γ (φ t))) =
      ∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second W Z (η t) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [hp t (Ioo_subset_Icc_self ht)]
  rw [heq] at hcancel
  exact hcancel

end PoincareConjecture.Topology.Surface
