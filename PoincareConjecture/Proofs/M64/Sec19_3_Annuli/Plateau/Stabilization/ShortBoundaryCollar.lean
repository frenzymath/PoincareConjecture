import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeRectangle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.SmoothAnnulusAdmission
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.AreaDensityProduct













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_short_boundary_collar
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M)) (S : ℝ) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (gamma beta : ℝ → M),
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma →
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 beta →
        Function.Periodic gamma curvePeriod → Function.Periodic beta curvePeriod →
        (∀ x ∈ Icc (0 : ℝ) curvePeriod,
          g.tangentNorm (gamma x) (curveVelocity gamma x) ≤ S) →
        (∀ x ∈ Icc (0 : ℝ) curvePeriod,
          g.tangentNorm (beta x) (curveVelocity beta x) ≤ S) →
        ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ rho →
          (∀ x, g.edist (gamma x) (beta x) ≤ ENNReal.ofReal epsilon) →
          ∃ A : M64Annulus g gamma beta, A.area ≤ C * epsilon := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨r, hr, H, hH, hgeom, -, -⟩ :=
    M63.exists_smooth_minimizing_interpolator g hcompact
  obtain ⟨B, hB, hbound⟩ :=
    m64_interpolator_endpoint_bound_on_short_tube g hcompact hr H hH S
  refine ⟨r / 2, half_pos hr, B * volume.real m64AnnulusDomain + 1,
    by positivity, ?_⟩
  intro gamma beta hgamma hbeta hpergamma hperbeta hspeedgamma hspeedbeta
    epsilon hepsilon hepsr hshort
  have hhalf (x : ℝ) : g.edist (gamma x) (beta x) ≤ ENNReal.ofReal (r / 2) :=
    (hshort x).trans (ENNReal.ofReal_le_ofReal hepsr)
  have hshortR (x : ℝ) : g.edist (gamma x) (beta x) < ENNReal.ofReal r :=
    (hhalf x).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  let input : LoopPlane → ℝ × (M × M) := fun p => (p 1, gamma (p 0), beta (p 0))
  let V : Set (ℝ × (M × M)) :=
    Ioo (-1 : ℝ) 2 ×ˢ {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}
  let U : Set LoopPlane := input ⁻¹' V
  let f : LoopPlane → M := H ∘ input
  have hcoord (i : Fin 2) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun p : LoopPlane => p i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff.contMDiff
  have hinput : ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) 1 input :=
    (hcoord 1).prodMk ((hgamma.comp (hcoord 0)).prodMk (hbeta.comp (hcoord 0)))
  have hV : IsOpen V := isOpen_Ioo.prod (isOpen_lt continuous_edist continuous_const)
  have hU : IsOpen U := hV.preimage hinput.continuous
  have hdom : m64AnnulusDomain ⊆ U := by
    intro p hp
    exact ⟨⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩, hshortR (p 0)⟩
  have hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U :=
    (hH.of_le (m := 1) (by simp)).comp hinput.contMDiffOn (fun _ hp => hp)
  have hperiodic (x s : ℝ) : f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s) := by
    change H (s, gamma (x + curvePeriod), beta (x + curvePeriod)) =
      H (s, gamma x, beta x)
    rw [hpergamma x, hperbeta x]
  have hlower (x : ℝ) : f (annulusPoint x 0) = gamma x :=
    (hgeom _ _ (hshortR x)).1
  have hupper (x : ℝ) : f (annulusPoint x 1) = beta x :=
    (hgeom _ _ (hshortR x)).2.1
  obtain ⟨A, hA⟩ := m64Annulus_exists_eq_of_contMDiffOn g hU hdom hf
    hperiodic hlower hupper
  refine ⟨A, ?_⟩
  have hdensity (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      m60AreaDensity g A.map p ≤ B * epsilon := by
    rw [hA]
    have hfat := (hf.contMDiffAt (hU.mem_nhds (hdom hp))).mdifferentiableAt one_ne_zero
    have hHat := (hH.contMDiffAt (hV.mem_nhds (hdom hp))).mdifferentiableAt (by simp)
    have hhor : g.tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B := by
      dsimp only [f, input, Function.comp_def]
      rw [m64_interpolator_horizontal_column_eq p
        (hgamma.mdifferentiable one_ne_zero _) (hbeta.mdifferentiable one_ne_zero _) hHat]
      exact hbound (p 1) ⟨hp.2.2.1, hp.2.2.2⟩ _ _ (hhalf (p 0))
        _ (hspeedgamma (p 0) ⟨hp.1, hp.2.1⟩)
        _ (hspeedbeta (p 0) ⟨hp.1, hp.2.1⟩)
    have hver : g.tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤
          epsilon := by
      rw [m64_local_cone_vertical_column_eq_slice hfat]
      change g.tangentNorm (H (p 1, gamma (p 0), beta (p 0)))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (fun s => H (s, gamma (p 0), beta (p 0))) (p 1) 1) ≤ epsilon
      rw [(hgeom _ _ (hshortR (p 0))).2.2.2.1 (p 1)
        ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩]
      exact (ENNReal.toReal_le_toReal (ne_top_of_lt (hshortR _)) ENNReal.ofReal_ne_top).mpr
        (hshort _) |>.trans_eq (ENNReal.toReal_ofReal hepsilon)
    exact (m60AreaDensity_le_tangentNorm_product g f p).trans
      (mul_le_mul hhor hver (Real.sqrt_nonneg _) hB)
  have harea := m64AnnulusIntegral_le_of_ae_density_bound
    m64AnnulusDomain_volume_ne_top A.area_integrable
      ((ae_restrict_mem m64AnnulusDomain_measurableSet).mono hdensity)
  change (∫ p in m64AnnulusDomain, m60AreaDensity g A.map p) ≤ _
  exact harea.trans (by nlinarith)

end PoincareConjecture.M64
