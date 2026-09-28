import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusClosedConformality
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzDerivative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M64

private theorem annulus_gram_diagonal_le_lipschitz
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {p : LoopPlane} (hp : p ∈ interior m64AnnulusDomain) (i : Fin 2) :
    m60AreaGram g A.map p i i ≤ (2 * A.lipschitz_constant) ^ 2 := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  let K : ℝ≥0 := ⟨A.lipschitz_constant, A.lipschitz_nonnegative⟩
  have hLip : LipschitzOnWith K A.map (interior m64AnnulusDomain) := by
    intro x hx y hy
    change g.edist (A.map x) (A.map y) ≤ _
    rw [edist_dist, dist_eq_norm, ENNReal.coe_nnreal_eq]
    change g.edist (A.map x) (A.map y) ≤
      ENNReal.ofReal A.lipschitz_constant * ENNReal.ofReal ‖x - y‖
    exact A.lipschitz_on_domain ⟨x, interior_subset hx⟩ ⟨y, interior_subset hy⟩
  have hb := M60.norm_mfderiv_apply_le_of_lipschitzOn
    (F := EuclideanSpace ℝ (Fin n)) isOpen_interior hLip hp
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  rw [(EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one] at hb
  change inner ℝ (mfderiv (𝓡 2) (𝓡 n) A.map p
      (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ i)) ≤ _
  rw [real_inner_self_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem annulus_phase_lipschitzOn
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map (interior m64AnnulusDomain))
    (L : LoopPlane → ℝ) (hL : Continuous L)
    (hL1 : ContDiffOn ℝ 1 L (interior m64AnnulusDomain))
    (hquot : ∀ p ∈ m64AnnulusDomain, P.circle.quotient (L p) = (A.map p).2) :
    LipschitzOnWith ⟨4 * A.lipschitz_constant,
      mul_nonneg (by norm_num) A.lipschitz_nonnegative⟩ L m64AnnulusDomain := by
  have hnonneg := A.lipschitz_nonnegative
  have hd (p : LoopPlane) (hp : p ∈ interior m64AnnulusDomain) :
      DifferentiableAt ℝ L p :=
    ((hL1 p hp).contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt one_ne_zero
  have hcol (p : LoopPlane) (hp : p ∈ interior m64AnnulusDomain) (i : Fin 2) :
      ‖fderiv ℝ L p (EuclideanSpace.single i 1)‖ ≤ 2 * A.lipschitz_constant := by
    have hq : P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ A.map := by
      filter_upwards [isOpen_interior.mem_nhds hp] with q hq
      exact hquot q (interior_subset hq)
    have hh := (local_circle_phase_column_sq_le_gram P t A.map L p
      (((hA p hp).contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt one_ne_zero)
      (hd p hp) hq i).trans (annulus_gram_diagonal_le_lipschitz A hp i)
    have hnonneg : 0 ≤ 2 * A.lipschitz_constant := by positivity
    rw [EuclideanSpace.basisFun_apply] at hh
    simpa only [Real.norm_eq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hnonneg).mp (by simpa only [sq_abs] using hh)
  have hbound (p : LoopPlane) (hp : p ∈ interior m64AnnulusDomain) :
      ‖fderiv ℝ L p‖ ≤ 4 * A.lipschitz_constant := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hv : v = v 0 • EuclideanSpace.single (0 : Fin 2) 1 +
        v 1 • EuclideanSpace.single (1 : Fin 2) 1 := by
      ext i
      fin_cases i <;> simp
    calc
      ‖fderiv ℝ L p v‖ = ‖v 0 • fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1) +
          v 1 • fderiv ℝ L p (EuclideanSpace.single (1 : Fin 2) 1)‖ := by
        conv_lhs => rw [hv, map_add, map_smul, map_smul]
      _ ≤ ‖v 0‖ * ‖fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)‖ +
          ‖v 1‖ * ‖fderiv ℝ L p (EuclideanSpace.single (1 : Fin 2) 1)‖ := by
        simpa only [norm_smul] using norm_add_le
          (v 0 • fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1))
          (v 1 • fderiv ℝ L p (EuclideanSpace.single (1 : Fin 2) 1))
      _ ≤ ‖v‖ * (2 * A.lipschitz_constant) + ‖v‖ * (2 * A.lipschitz_constant) :=
        add_le_add (mul_le_mul (PiLp.norm_apply_le v 0) (hcol p hp 0)
          (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (PiLp.norm_apply_le v 1) (hcol p hp 1)
            (norm_nonneg _) (norm_nonneg _))
      _ = (4 * A.lipschitz_constant) * ‖v‖ := by ring
  have hLip : LipschitzOnWith ⟨4 * A.lipschitz_constant, by positivity⟩
      L (interior m64AnnulusDomain) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le hd (fun p hp => hbound p hp)
      m64AnnulusDomain_convex.interior
  have hsub : m64AnnulusInterior ⊆ interior m64AnnulusDomain := by
    apply interior_maximal _ isOpen_m64AnnulusInterior
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hclosure : m64AnnulusDomain ⊆ closure (interior m64AnnulusDomain) := by
    calc
      m64AnnulusDomain = closure m64AnnulusInterior := m64AnnulusInterior_closure.symm
      _ ⊆ closure (interior m64AnnulusDomain) := closure_mono hsub
  exact (LipschitzOnWith.closure hL.continuousOn hLip).mono hclosure

end PoincareConjecture.M64
