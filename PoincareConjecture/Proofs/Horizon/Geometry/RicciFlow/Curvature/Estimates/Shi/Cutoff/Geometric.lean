import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Induction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Cutoff.CappedDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Cutoff.Profile
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Cutoff.SpatialSupport


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def shiRetainedFlowRadius (n : ℕ) (alpha delta : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * alpha) * delta / 4

noncomputable def shiGeometricScale (n : ℕ) (K t rho : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * K * t) / rho

noncomputable def shiGeometricCutoff
    (n : ℕ) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (K alpha delta : ℝ) {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    (p : M) (t : ℝ) (y : M) : ℝ :=
  shiCutoffProfile
    (shiGeometricScale n K t (shiRetainedFlowRadius n alpha delta) *
      shiCappedDistance (F.metric t) p
        (shiRetainedFlowRadius n alpha delta) y)

theorem shiRetainedFlowRadius_pos
    {alpha delta : ℝ} (hdelta : 0 < delta) :
    0 < shiRetainedFlowRadius n alpha delta := by
  unfold shiRetainedFlowRadius
  positivity

theorem shiGeometricScale_pos
    {K alpha delta t : ℝ} (hdelta : 0 < delta) :
    0 < shiGeometricScale n K t (shiRetainedFlowRadius n alpha delta) := by
  unfold shiGeometricScale
  exact div_pos (Real.exp_pos _) (shiRetainedFlowRadius_pos hdelta)

theorem shiGeometricCutoff_nonneg
    {K alpha delta T : ℝ} {F : RicciFlow n M (Icc 0 T)}
    {p y : M} {t : ℝ} (hdelta : 0 < delta) :
    0 ≤ shiGeometricCutoff n K alpha delta F p t y := by
  unfold shiGeometricCutoff
  exact (shiCutoffProfile_mem_Icc _).1

theorem shiGeometricCutoff_le_one
    {K alpha delta T : ℝ} {F : RicciFlow n M (Icc 0 T)}
    {p y : M} {t : ℝ} (hdelta : 0 < delta) :
    shiGeometricCutoff n K alpha delta F p t y ≤ 1 := by
  unfold shiGeometricCutoff
  exact (shiCutoffProfile_mem_Icc _).2

theorem shiPhysicalCutoffSupports_of_local
    (g : ℝ → RiemannianMetric n M)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {T : ℝ} {C : Set M} {eta : ℝ → M → ℝ} {L G : ℝ}
    (hlocal : ∀ t ∈ Ioc 0 T, ∀ x ∈ interior C, 0 < eta t x →
      ∀ ε > 0, ∃ e : ℝ → M → ℝ, ∃ ed : ℝ, ∃ U : Set M,
        IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (e t) U ∧
        e t x = eta t x ∧ (∀ᶠ y in 𝓝 x, e t y ≤ eta t y) ∧
        (∀ᶠ s in 𝓝[Icc 0 t] t, e s x ≤ eta s x) ∧
        HasDerivWithinAt (fun s => e s x) ed (Icc 0 t) t ∧
        scalarGradientSq (g t) (e t) x ≤ G * eta t x ∧
        ed - (D t).laplacian (e t) x ≤ L + ε) :
    shiPhysicalCutoffSupports g D T C eta L G := by
  intro t ht x hx hpos ε hε
  exact hlocal t ht x hx hpos ε hε

theorem exists_shi_geometric_cutoff (n : ℕ) (K alpha delta : ℝ)
    (hK : 0 < K) (hdelta : 0 < delta) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧
      ∀ (N : Type u) [TopologicalSpace N]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
        [T2Space N],
      ∀ (T : ℝ), 0 ≤ T → T ≤ alpha / K →
      ∀ (F : RicciFlow n N (Icc 0 T)) (p : N) (C : Set N),
        IsCompact C →
        (∀ t ∈ Icc 0 T,
          closure ((F.metric t).ball p (shiRetainedFlowRadius n alpha delta)) ⊆ C) →
        (∀ t ∈ Icc 0 T, ∀ y ∈ C, (F.connection t).curvatureTensorNorm y ≤ K) →
        p ∈ C ∧ ∃ η : ℝ → N → ℝ,
          ContinuousOn (Function.uncurry η) (Icc 0 T ×ˢ C) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C, 0 ≤ η t y) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C, η t y ≤ 1) ∧
          (∀ t ∈ Icc 0 T, ∀ y ∈ C \ interior C, η t y = 0) ∧
          (∀ t ∈ Icc 0 T, η t p = 1) ∧
          shiPhysicalCutoffSupports F.metric F.connection T C η L G := by
  obtain ⟨C₁, C₂, Gp, hC₁, hC₂, hGp, hprofile⟩ := exists_shiCutoffProfile_bounds
  let R := shiRetainedFlowRadius n alpha delta
  let B := Real.exp ((n : ℝ) * alpha) / R
  let L := (2 * (n : ℝ) * C₁ + C₂) * B ^ 2 + C₁ * (n : ℝ) * K
  let G := Gp * B ^ 2
  have hR : 0 < R := shiRetainedFlowRadius_pos hdelta
  have hB : 0 < B := div_pos (Real.exp_pos _) hR
  refine ⟨L, G, ?_, ?_, ?_⟩
  · dsimp only [L]
    positivity
  · exact mul_nonneg hGp.le (sq_nonneg B)
  intro N _ _ _ _ T hT hTK F p C hC hflow hRm
  let b : ℝ → ℝ := fun t => shiGeometricScale n K t R
  let f : ℝ → N → ℝ := fun t y => shiCappedDistance (F.metric t) p R y
  let η : ℝ → N → ℝ := fun t y => shiCutoffProfile (b t * f t y)
  have hb (t : ℝ) : 0 < b t := div_pos (Real.exp_pos _) hR
  have hcap {t : ℝ} (ht : t ∈ Icc 0 T) : 1 ≤ b t * R := by
    dsimp only [b, shiGeometricScale]
    rw [div_mul_cancel₀ _ (ne_of_gt hR)]
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hK.le) ht.1)
  have hbmax {t : ℝ} (ht : t ∈ Icc 0 T) : b t ≤ B := by
    apply div_le_div_of_nonneg_right _ hR.le
    apply Real.exp_le_exp.mpr
    have htK : t * K ≤ alpha := (le_div_iff₀ hK).mp (ht.2.trans hTK)
    have hc := mul_le_mul_of_nonneg_left htK (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    nlinarith only [hc]
  have hretain : ∀ t ∈ Icc 0 T, (F.metric t).ball p R ⊆ C := by
    intro t ht y hy
    exact hflow t ht (subset_closure hy)
  have hself (t : ℝ) : (F.metric t).edist p p = 0 := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_self
  have hpball (t : ℝ) : p ∈ (F.metric t).ball p R := by
    change (F.metric t).edist p p < ENNReal.ofReal R
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hR
  have hηp (t : ℝ) : η t p = 1 := by
    dsimp only [η, f]
    rw [shiCappedDistance_eq_of_mem_ball (hpball t), hself,
      ENNReal.toReal_zero, mul_zero]
    exact shiCutoffProfile_one (by norm_num)
  have hη0 (t : ℝ) (y : N) : 0 ≤ η t y := (shiCutoffProfile_mem_Icc _).1
  have hη1 (t : ℝ) (y : N) : η t y ≤ 1 := (shiCutoffProfile_mem_Icc _).2
  have hηspace (t : ℝ) : Continuous (η t) :=
    shiCutoffProfile_smooth.continuous.comp
      (continuous_const.mul (continuous_shiCappedDistance (F.metric t) p R))
  have hηC : ContinuousOn (Function.uncurry η) (Icc 0 T ×ˢ C) := by
    have hf := continuousOn_shiCappedDistance_flow F hK.le hR p hretain hRm
    have hbcont : Continuous (fun z : ℝ × N => b z.1) := by
      dsimp only [b, shiGeometricScale]
      fun_prop
    exact shiCutoffProfile_smooth.continuous.comp_continuousOn
      ((hbcont.continuousOn.mul hf).mono (fun z hz => ⟨hz.1, mem_univ z.2⟩))
  have hpositive {t : ℝ} (ht : t ∈ Icc 0 T) {y : N} (hy : 0 < η t y) :
      y ∈ (F.metric t).ball p R := by
    by_contra hnot
    have hd := shiCappedDistance_eq_of_le_edist hR.le (le_of_not_gt hnot)
    have hz : η t y = 0 := by
      dsimp only [η, f]
      rw [hd]
      exact shiCutoffProfile_zero (hcap ht)
    exact (ne_of_gt hy) hz
  have hboundary : ∀ t ∈ Icc 0 T, ∀ y ∈ C \ interior C, η t y = 0 := by
    intro t ht y hy
    apply le_antisymm _ (hη0 t y)
    by_contra hnot
    have hpos : 0 < η t y := lt_of_not_ge hnot
    apply hy.2
    exact mem_interior.mpr ⟨{z | 0 < η t z},
      (fun z hz => hretain t ht (hpositive ht hz)),
      isOpen_lt continuous_const (hηspace t), hpos⟩
  have hpast {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
      (hst : s ≤ t) (y : N) : η t y ≤ η s y := by
    apply shiCutoffProfile_antitone
    have hh := shiCappedDistance_flow_comparison F hK.le hR p hretain hRm hs ht y
    rw [abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hst)] at hh
    have he : b s * Real.exp ((n : ℝ) * K * (t - s)) = b t := by
      dsimp only [b, shiGeometricScale]
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    calc
      b s * f s y ≤ b s * (Real.exp ((n : ℝ) * K * (t - s)) * f t y) :=
        mul_le_mul_of_nonneg_left hh (hb s).le
      _ = b t * f t y := by rw [← mul_assoc, he]
  refine ⟨hretain 0 ⟨le_rfl, hT⟩ (hpball 0), η, hηC,
    (fun t _ y _ => hη0 t y), (fun t _ y _ => hη1 t y), hboundary,
    (fun t _ => hηp t), ?_⟩
  intro t ht y hy hpos ε hε
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
  have hcurrent : IsCompact (closure ((F.metric t).ball p R)) :=
    hC.of_isClosed_subset isClosed_closure (hflow t ht')
  obtain ⟨V, v, hV, hyV, hv, hveq, hvle, hvgrad, hvlap⟩ :=
    exists_shi_spatial_cutoff_lower_support (F.connection t) p y
      hR hK.le (hb t) (hcap ht') hcurrent
      (fun z hz => hRm t ht' z (hretain t ht' hz))
      hC₁ hC₂.le hGp.le hprofile hpos hε
  refine ⟨fun _ z => v z, 0, V, hV, hyV, hv, hveq, hvle, ?_, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hveq]
    exact hpast ⟨hs.1, hs.2.trans ht.2⟩ ht' hs.2 y
  · exact hasDerivWithinAt_const t (Icc 0 t) (v y)
  · have hb2 : b t ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (hb t).le hB.le).2 (hbmax ht')
    exact hvgrad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb2 hGp.le) hpos.le)
  · have hb2 : b t ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (hb t).le hB.le).2 (hbmax ht')
    have hcoeff : 0 ≤ 2 * (n : ℝ) * C₁ + C₂ := by positivity
    simpa only [zero_sub, L] using hvlap.trans
      (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hb2 hcoeff) le_rfl) le_rfl)

end PoincareConjecture.RicciFlowAnalysis
