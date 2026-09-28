import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeInterpolator
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTraceEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem m64_local_cone_vertical_column_eq_slice {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p) :
    mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => f (annulusPoint (p 0) s)) (p 1) 1 := by
  have hline : HasDerivAt (annulusPoint (p 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) (p 1) := by
    convert m64AnnulusPoint_vertical_hasDerivAt (p 0) (p 1) using 1
    ext i
    fin_cases i <;> simp [EuclideanSpace.basisFun_apply]
  have hp : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (annulusPoint (p 0)) (p 1) 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hline.deriv
  have hc := mfderiv_comp_apply_of_eq (p 1) hf
    hline.differentiableAt.mdifferentiableAt hp (1 : ℝ)
  rw [hd] at hc
  exact hc.symm

variable [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem m64_exists_local_cone_rectangles
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M)) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (gamma : ℝ → M) (center : M), ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma →
        Function.Periodic gamma curvePeriod →
        (∀ x, g.edist center (gamma x) ≤ ENNReal.ofReal delta) →
        ∃ f : LoopPlane → M,
          (∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 n) 1 f p) ∧
          (∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s)) ∧
          (∀ x, f (annulusPoint x 0) = center) ∧
          (∀ x, f (annulusPoint x 1) = gamma x) ∧
          ∀ p ∈ m64AnnulusDomain,
            m60EnergyDensity g f p ≤
              (B ^ 2 * (g.tangentNorm (gamma (p 0)) (curveVelocity gamma (p 0))) ^ 2 +
                (g.edist center (gamma (p 0))).toReal ^ 2) / 2 := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨r, hr, B, hB, H, hH, hgeom, _⟩ := m64_exists_local_cone_interpolator g hcompact
  have hU : IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
    isOpen_lt continuous_edist continuous_const
  refine ⟨r / 2, half_pos hr, B, hB, ?_⟩
  intro gamma center hgamma hperiod hshort
  let f : LoopPlane → M := fun p => H (p 1, center, gamma (p 0))
  have hHat (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H
        (p 1, center, gamma (p 0)) := by
    apply (hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ?_)).of_le (by simp)
    exact ⟨⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩,
      (hshort (p 0)).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))⟩
  have hfat (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      ContMDiffAt (𝓡 2) (𝓡 n) 1 f p := by
    have hp0 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun z : LoopPlane => z 0) p :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.contMDiff.contMDiffAt
    have hp1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun z : LoopPlane => z 1) p :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.contMDiff.contMDiffAt
    exact (hHat p hp).comp p (hp1.prodMk
      (contMDiffAt_const.prodMk (hgamma.contMDiffAt.comp p hp0)))
  refine ⟨f, hfat, ?_, ?_, ?_, ?_⟩
  · intro x s
    change H (s, center, gamma (x + curvePeriod)) = H (s, center, gamma x)
    rw [hperiod x]
  · intro x
    exact (hgeom center (gamma x) (hshort x)).1
  · intro x
    exact (hgeom center (gamma x) (hshort x)).2.1
  · intro p hp
    have htime : p 1 ∈ Icc (0 : ℝ) 1 := ⟨hp.2.2.1, hp.2.2.2⟩
    have hhor : g.tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤
        B * g.tangentNorm (gamma (p 0)) (curveVelocity gamma (p 0)) := by
      rw [m64_interpolator_horizontal_column_eq (gamma := fun _ => center)
        (beta := gamma) p mdifferentiableAt_const
        (hgamma.mdifferentiable one_ne_zero _) ((hHat p hp).mdifferentiableAt one_ne_zero)]
      have hz : curveVelocity (n := n) (fun _ : ℝ => center) (p 0) = 0 := by
        simp only [curveVelocity, mfderiv_const, zero_apply]
      rw [hz]
      exact (hgeom center (gamma (p 0)) (hshort (p 0))).2.2.2 (p 1) htime _
    have hver : g.tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
        (g.edist center (gamma (p 0))).toReal := by
      rw [m64_local_cone_vertical_column_eq_slice ((hfat p hp).mdifferentiableAt one_ne_zero)]
      exact (hgeom center (gamma (p 0)) (hshort (p 0))).2.2.1 (p 1) htime
    have hnonneg : 0 ≤ g.tangentNorm (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :=
      Real.sqrt_nonneg _
    have hsquare := mul_self_le_mul_self hnonneg hhor
    have hgram (i : Fin 2) : m60AreaGram g f p i i =
        (g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ i))) ^ 2 := by
      change inner ℝ (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
          ‖mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2
      exact real_inner_self_eq_norm_sq _
    rw [m60EnergyDensity, Matrix.trace_fin_two, hgram 0, hgram 1, hver]
    nlinarith

end PoincareConjecture
