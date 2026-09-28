import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Support

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem exists_mulSmooth_norm_bound_of_compact_closure (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) :
    ∃ C ≥ 0, ∀ f : EnergyTest D Ω, ‖f.mulSmooth χ hχ‖ ≤ C * ‖f‖ := by
  classical
  obtain ⟨s, ρ, hρc, _⟩ := exists_finite_chart_partition (n := n) hc
  let A : EnergyTest D Ω →L[ℝ] EnergyTest D Ω :=
    ∑ i, mulSmoothCLM D Ω (fun x => ρ i x * χ x)
      ((ρ i).contMDiff.mul hχ) ((hρc i).mul_right)
  have hA (f : EnergyTest D Ω) : A f = f.mulSmooth χ hχ := by
    have h := (f.mulSmooth χ hχ).sum_mul_partition ρ subset_closure
    convert h using 1
    simp only [A, sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Subtype.ext
    funext x
    exact mul_assoc _ _ _
  exact ⟨‖A‖, norm_nonneg A, fun f => by rw [← hA]; exact A.le_opNorm f⟩

def domainMulSmoothCLM (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) :
    EnergyTest D Ω →L[ℝ] EnergyTest D Ω :=
  (mulSmoothLinear D Ω χ hχ).mkContinuous
    (exists_mulSmooth_norm_bound_of_compact_closure (D := D) hc χ hχ).choose
    (exists_mulSmooth_norm_bound_of_compact_closure (D := D) hc χ hχ).choose_spec.2

@[simp] theorem domainMulSmoothCLM_apply (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (f : EnergyTest D Ω) :
    domainMulSmoothCLM D Ω hc χ hχ f = f.mulSmooth χ hχ := rfl

def energyMulSmooth (D : LeviCivitaData g) (Ω : Set M)
    (hc : IsCompact (closure Ω)) (χ : M → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) : H1Zero D Ω →L[ℝ] H1Zero D Ω :=
  Poincare.Analysis.Dirichlet.completionMap
    (Completion.toComplL.comp (domainMulSmoothCLM D Ω hc χ hχ))

@[simp] theorem energyMulSmooth_coe (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (f : EnergyTest D Ω) :
    energyMulSmooth D Ω hc χ hχ (f : H1Zero D Ω) =
      (f.mulSmooth χ hχ : H1Zero D Ω) := by
  simp [energyMulSmooth]

private def boundedMulL2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  have hm (f : Lp ℝ 2 μ) : MemLp (fun x => a x * f x) 2 μ :=
    (Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
      (hC.mono fun x hx => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  exact LinearMap.mkContinuous
    { toFun := fun f => (hm f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (fun f => Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [(hm f).coeFn_toLp, hC] with x hx hax
      change ‖((hm f).toLp _) x‖ ≤ C * ‖f x‖
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right hax (norm_nonneg _))

private theorem boundedMulL2_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a : X → ℝ) (ha : AEStronglyMeasurable a μ) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : Lp ℝ 2 μ) :
    (boundedMulL2 a ha C hC f : X → ℝ) =ᵐ[μ] fun x => a x * f x := by
  have hm : MemLp (fun x => a x * f x) 2 μ :=
    (Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
      (hC.mono fun x hx => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  exact hm.coeFn_toLp

private theorem exists_domain_mul_bound (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : Continuous χ) :
    ∃ C : ℝ, ∀ᵐ x ∂g.volumeMeasure.restrict Ω, ‖χ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hχ.continuousOn
  exact ⟨C, (ae_restrict_mem hΩ.measurableSet).mono fun x hx => hC x (subset_closure hx)⟩

def domainMulL2 (g : RiemannianMetric n M) (Ω : Set M)
    (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) (χ : M → ℝ) (hχ : Continuous χ) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  boundedMulL2 χ hχ.aestronglyMeasurable
    (exists_domain_mul_bound (g := g) hΩ hc χ hχ).choose
    (exists_domain_mul_bound (g := g) hΩ hc χ hχ).choose_spec

theorem domainMulL2_ae (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : Continuous χ) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (domainMulL2 g Ω hΩ hc χ hχ f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      fun x => χ x * f x :=
  boundedMulL2_ae _ _ _ _ _

theorem memLp_continuous_mul (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : Continuous χ) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    MemLp (fun x => χ x * f x) 2 (g.volumeMeasure.restrict Ω) :=
  MemLp.ae_eq (domainMulL2_ae hΩ hc χ hχ f)
    (Lp.memLp (domainMulL2 g Ω hΩ hc χ hχ f))

theorem norm_domainMulL2 (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : Continuous χ) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ‖domainMulL2 g Ω hΩ hc χ hχ f‖ =
      (eLpNorm (fun x => χ x * f x) 2 (g.volumeMeasure.restrict Ω)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (domainMulL2_ae hΩ hc χ hχ f)]

theorem domainMulL2_inner (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : Continuous χ) (f k : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ⟪domainMulL2 g Ω hΩ hc χ hχ f, k⟫_ℝ =
      ⟪f, domainMulL2 g Ω hΩ hc χ hχ k⟫_ℝ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [domainMulL2_ae hΩ hc χ hχ f, domainMulL2_ae hΩ hc χ hχ k]
    with x hf hk
  simp only [hf, hk, RCLike.inner_apply, conj_trivial]
  ring

theorem domainMulL2_mul (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ η : M → ℝ) (hχ : Continuous χ) (hη : Continuous η)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    domainMulL2 g Ω hΩ hc (fun x => χ x * η x) (hχ.mul hη) f =
      domainMulL2 g Ω hΩ hc χ hχ (domainMulL2 g Ω hΩ hc η hη f) := by
  apply Lp.ext
  filter_upwards [domainMulL2_ae hΩ hc (fun x => χ x * η x) (hχ.mul hη) f,
    domainMulL2_ae hΩ hc χ hχ (domainMulL2 g Ω hΩ hc η hη f),
    domainMulL2_ae hΩ hc η hη f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]

theorem toDomainL2_energyMulSmooth (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (u : H1Zero D Ω) :
    toDomainL2 D Ω (energyMulSmooth D Ω hc χ hχ u) =
      domainMulL2 g Ω hΩ hc χ hχ.continuous (toDomainL2 D Ω u) := by
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((toDomainL2 D Ω).continuous.comp (energyMulSmooth D Ω hc χ hχ).continuous)
      ((domainMulL2 g Ω hΩ hc χ hχ.continuous).continuous.comp (toDomainL2 D Ω).continuous)
  | ih f =>
    rw [energyMulSmooth_coe]
    apply Lp.ext
    filter_upwards [toDomainL2_ae (f.mulSmooth χ hχ : H1Zero D Ω),
      toDomainL2_ae (f : H1Zero D Ω),
      domainMulL2_ae hΩ hc χ hχ.continuous (toDomainL2 D Ω f),
      ae_restrict_of_ae (f.mulSmooth χ hχ).memLp.coeFn_toLp,
      ae_restrict_of_ae f.memLp.coeFn_toLp] with x h₁ h₂ h₃ h₄ h₅
    rw [h₃, h₁, h₂, toL2_coe, toL2_coe]
    exact h₄.trans (congrArg (fun y : ℝ => χ x * y) h₅.symm)

end PoincareConjecture.LeviCivitaData.Dirichlet
