import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedSampling
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeAngle
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_uniform_positive_rounded_tube_projection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    {K : Set ℝ} (hK : IsCompact K) {c d : ℝ → ℝ → E} {l u : ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => c p.1 p.2) (K ×ˢ Icc (l - 1) (u + 1)))
    (hd : ∀ z ∈ K, ∀ s ∈ Icc (l - 1) (u + 1), HasDerivAt (c z) (d z s) s)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => d p.1 p.2) (K ×ˢ Icc (l - 1) (u + 1)))
    (htarget : ∀ z ∈ K, ∀ s ∈ Icc l u, (z, c z s) ∈ T.target)
    (hproj : ∀ z ∈ K, ∀ s : ℝ,
      curveTubeProjection q0 T (z, c z s) = sphereCircleParameter e s) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ h : ℝ, 0 < h → h < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ ρ : ℝ → ℝ, Differentiable ℝ ρ →
          (∀ s, δ ≤ |s| → ρ s = |s|) →
          (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
          (∀ s, |deriv ρ s| ≤ 1) → ∀ z ∈ K,
            let G : ℝ → E := fun t => roundedVertexPath ρ (fun i : ℤ => c z (h * i)) (t / h)
            ∀ s ∈ Icc l u, ((z, s), G s) ∈ curveTubeAngularDomain e q0 T ∧
              0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (G s) (deriv G s) := by
  let A := curveTubeAngle e q0 T
  let V := curveTubeAngularDomain e q0 T
  let D : (ℝ × ℝ) × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (fun y : E => A (p.1, y)) p.2
  obtain ⟨hV, _⟩ := curveTubeAngle_regular e q0 T hInv hx
  have hD : ContinuousOn D V := (contDiffOn_fderiv_curveTubeAngle e q0 T hInv hx).continuousOn
  let B : Set ((ℝ × ℝ) × (E × E)) := {p | (p.1, p.2.1) ∈ V}
  let J : (ℝ × ℝ) × (E × E) → ℝ := fun p => D (p.1, p.2.1) p.2.2
  have hB : IsOpen B := hV.preimage (continuous_fst.prodMk continuous_snd.fst)
  have hJ : ContinuousOn J B :=
    (hD.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      (fun _ hp => hp)).clm_apply continuous_snd.snd.continuousOn
  let W := B ∩ J ⁻¹' Ioi 0
  have hW : IsOpen W := hJ.isOpen_inter_preimage hB isOpen_Ioi
  have hwide {s : ℝ} (hs : s ∈ Icc l u) : s ∈ Icc (l - 1) (u + 1) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbase : ∀ z ∈ K, ∀ s ∈ Icc l u, ((z, s), (c z s, d z s)) ∈ W := by
    intro z hz s hs
    have hmem := mem_curveTubeAngularDomain_of_projection e q0 T z s s (c z s)
      (htarget z hz s hs) (hproj z hz s)
      (show s - s ∈ Ioo (-Real.pi) Real.pi by simp [Real.pi_pos])
    refine ⟨hmem, ?_⟩
    have hcal := fderiv_curveTubeAngle_apply_velocity e q0 T hInv hx (c z) z s
      (hd z hz s (hwide hs)).differentiableAt (htarget z hz s hs) (hproj z hz)
    rw [(hd z hz s (hwide hs)).deriv] at hcal
    change 0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y)) (c z s) (d z s)
    rw [hcal]
    norm_num
  have hsub : K ×ˢ Icc l u ⊆ K ×ˢ Icc (l - 1) (u + 1) := fun _ hp => ⟨hp.1, hwide hp.2⟩
  let F : ℝ × ℝ → (ℝ × ℝ) × (E × E) := fun p => (p, (c p.1 p.2, d p.1 p.2))
  have hF : ContinuousOn F (K ×ˢ Icc l u) :=
    continuousOn_id.prodMk ((hc.mono hsub).prodMk (hcont.mono hsub))
  have hcompact : IsCompact (F '' (K ×ˢ Icc l u)) :=
    (hK.prod isCompact_Icc).image_of_continuousOn hF
  have hinside : F '' (K ×ˢ Icc l u) ⊆ W := by
    rintro y ⟨⟨z, s⟩, ⟨hz, hs⟩, rfl⟩
    exact hbase z hz s hs
  obtain ⟨ε, hε, hthick⟩ := hcompact.exists_thickening_subset_open hW hinside
  obtain ⟨η, hη, hηhalf, hestimate⟩ := exists_uniform_rounded_sampling_estimates hK hc hd hcont hε
  refine ⟨η, hη, hηhalf, ?_⟩
  intro h hh hηh δ hδ hδhalf ρ hρ htail hbound hder z hz
  dsimp only
  intro s hs
  let G : ℝ → E := fun t => roundedVertexPath ρ (fun i : ℤ => c z (h * i)) (t / h)
  have hclose := hestimate h hh hηh δ hδ hδhalf ρ hρ htail hbound hder z hz s hs
  change ((z, s), (G s, deriv G s)) ∈ W
  apply hthick
  apply Metric.mem_thickening_iff.mpr
  refine ⟨F (z, s), ⟨(z, s), ⟨hz, hs⟩, rfl⟩, ?_⟩
  change dist ((z, s), (G s, deriv G s)) ((z, s), (c z s, d z s)) < ε
  rw [dist_prod_same_left, Prod.dist_eq]
  exact max_lt hclose.1 (by simpa only [dist_eq_norm] using hclose.2)

end PoincareConjecture.M25.Topology3D
