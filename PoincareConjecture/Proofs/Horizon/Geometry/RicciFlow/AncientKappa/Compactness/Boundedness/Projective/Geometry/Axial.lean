import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Pairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Threshold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [IsManifold (𝓡 3) ∞ M] in
theorem isOpen_image_slab {f : RoundCylinderSpace → M} {s : ℝ}
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-s) s)) : IsOpen (f '' (univ ×ˢ Ioo (-s) s)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨z, hz, rfl⟩
  rw [← hf.isLocalHomeomorphOn.map_nhds_eq hz]
  exact Filter.image_mem_map ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)

theorem hasDerivAt_comp_geodesic {g : RiemannianMetric 3 M}
    {U : Set M} (hU : IsOpen U) {a : M → ℝ}
    (ha : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a U)
    {γ : ℝ → M} {L : ℝ} (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hγU : ∀ t ∈ Icc 0 L, γ t ∈ U) {t : ℝ} (ht : t ∈ Icc 0 L) :
    HasDerivAt (a ∘ γ)
      (mvfderiv (𝓡 3) a (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) t := by
  have haa := ha.contMDiffAt (hU.mem_nhds (hγU t ht))
  have hfirst : HasDerivAt (a ∘ γ) (deriv (a ∘ γ) t) t := by
    apply DifferentiableAt.hasDerivAt
    apply (contMDiffAt_iff_contDiffAt.mp
      ((haa.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp t
        (hγ.contMDiffAt ht))).differentiableAt (by simp)
  have heq := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp t (haa.mdifferentiableAt (by simp))
      ((hγ.contMDiffAt ht).mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv] at heq
  change deriv (a ∘ γ) t =
    mvfderiv (𝓡 3) a (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) at heq
  rwa [heq] at hfirst

theorem long_geodesics_are_almost_axial_signed {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (f : RoundCylinderSpace → M) {ε r : ℝ},
        0 < ε → ε ≤ ε₀ → 0 < r →
        IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
          (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
        RoundCylinderClose ε 0
          (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w) →
        ∀ (a : M → ℝ),
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) →
        (∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2) →
        ∀ {γ : ℝ → M} {L : ℝ}, r / (100 * ε) < L →
        g.IsGeodesicOn γ (Icc 0 L) →
        (∀ t ∈ Icc 0 L, γ t ∈ f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) →
        (∀ t ∈ Icc 0 L,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) →
        (∀ b ∈ Icc (0 : ℝ) L, ∀ c ∈ Icc (0 : ℝ) L, b ≤ c →
          ENNReal.ofReal (c - b) ≤
            intrinsicEDist g (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (γ b) (γ c)) →
        ∀ {σ : ℝ}, |σ| = 1 → σ * a (γ 0) < σ * a (γ L) →
        ∀ t ∈ Icc 0 L, ∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, f z = γ t →
        g.tangentNorm (γ t)
          (σ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 -
            r⁻¹ • (show TangentSpace (𝓡 3) (γ t) from
              mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z (0, 1))) < α := by
  obtain ⟨K, hK⟩ := exists_axial_hessian_bound.{u}
  let C := Real.sqrt 2 * (Real.pi + 1)
  obtain ⟨β, ε₀, _, hε₀, hε₀half, hwindow⟩ :=
    EpsilonNeck.exists_axial_alignment_window_threshold K C (half_pos hα)
  refine ⟨ε₀, hε₀, hε₀half, ?_⟩
  intro M _ _ _ _ _ _ _ g D f ε r hε hε₀' hr hf hclose a ha hvalue
    γ L hL hγ hcarrier hunit hsegment σ hσ horient t ht z hz heq
  have hεhalf := hε₀'.trans_lt hε₀half
  have hU := isOpen_image_slab hf
  let F := a ∘ γ
  let acc := fun t => D.hessian a (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
  have hfirst (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt F (deriv F t) t :=
    (hasDerivAt_comp_geodesic hU ha hγ hcarrier ht).differentiableAt.hasDerivAt
  have hsecond (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt (deriv F) (acc t) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU ha hγ ht (hcarrier t ht)
  have hacc (t : ℝ) (ht : t ∈ Icc 0 L) : |σ * acc t| ≤ K * ε / r ^ 2 := by
    rw [abs_mul, hσ, one_mul]
    obtain ⟨z, hz, hzγ⟩ := hcarrier t ht
    have hh := hK g D f hε hεhalf hr hf hclose a ha hvalue hz.2
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
    rw [hzγ] at hh
    exact hh (hunit t ht)
  have hc (b : ℝ) (hb : b ∈ Icc 0 L) (c : ℝ) (hc : c ∈ Icc 0 L) (_ : b ≤ c) :
      intrinsicEDist g (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (γ b) (γ c) ≤
        ENNReal.ofReal (r * Real.sqrt (1 + ε) * (|σ * F c - σ * F b| + C)) := by
    obtain ⟨zb, hzb, hzbγ⟩ := hcarrier b hb
    obtain ⟨zc, hzc, hzcγ⟩ := hcarrier c hc
    have hh := intrinsicEDist_cylinderCover_le_axial_add g f hε
      (sq_pos_of_pos (inv_pos.mpr hr)) hf.contMDiffOn hclose hzb.2 hzc.2
    have hsqrt : Real.sqrt ((1 + ε) / r⁻¹ ^ 2) = r * Real.sqrt (1 + ε) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_sq (inv_pos.mpr hr).le,
        div_inv_eq_mul, mul_comm]
    have hvb : F b = zb.2 := by simpa only [F, Function.comp_apply, hzbγ] using hvalue zb hzb
    have hvc : F c = zc.2 := by simpa only [F, Function.comp_apply, hzcγ] using hvalue zc hzc
    rw [hzbγ, hzcγ, hsqrt] at hh
    simpa only [← mul_sub, abs_mul, hσ, one_mul, hvb, hvc, C] using hh
  have h := hwindow ε hε hε₀' r hr
  have hvel := EpsilonNeck.long_scaled_velocity_lower_bound_of_intrinsic_minimality
    g (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) hr hε hεhalf hL h.1 h.2.1
    (fun t ht => (hfirst t ht).const_mul σ)
    (fun t ht => (hsecond t ht).const_mul σ) hacc
    (show 0 ≤ C by dsimp [C]; positivity) hsegment hc horient t ht
  have hderiv := (hasDerivAt_comp_geodesic hU ha hγ hcarrier ht).deriv
  change deriv F t = _ at hderiv
  rw [hderiv] at hvel
  have hv : g.tangentNorm (f z) (σ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1 := by
    rw [heq]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hσ with hσ | hσ
    · simpa only [hσ, one_smul] using hunit t ht
    · simpa only [hσ, neg_smul, one_smul, RiemannianMetric.tangentNorm,
        map_neg, neg_apply, neg_neg] using hunit t ht
  have hvel' : 1 - β ≤ r * mvfderiv (𝓡 3) a (f z)
      (σ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) := by
    rw [heq]
    simpa only [map_smul, smul_eq_mul] using hvel
  have halign := cylinderCover_tangentNorm_sub_scaled_axial_le_of_velocity
    g hε.le hεhalf hr hf hclose ha hvalue hz.2 _ hv
    (half_pos hα).le hvel' h.2.2.le
  rw [heq] at halign
  exact halign.trans_lt (half_lt_self hα)

end PoincareConjecture.CylinderCover
