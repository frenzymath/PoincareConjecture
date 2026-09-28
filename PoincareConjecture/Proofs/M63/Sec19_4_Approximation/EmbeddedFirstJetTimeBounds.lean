import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedEquation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Adapters
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_uniform_embedded_firstJet_time_lipschitz [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {kappa V J1 : ℝ} (hkappa : 0 ≤ kappa) (hV : 0 ≤ V) (hJ1 : 0 ≤ J1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
      ∀ sigma tau : ℝ, a ≤ sigma → sigma ≤ tau → tau ≤ b →
      (∀ r ∈ Ioo sigma tau, ∀ x, m62Curvature F c r x ≤ kappa) →
      (∀ r ∈ Ioo sigma tau, ∀ x, curveSpeed F c r x ≤ V) →
      (∀ r ∈ Ioo sigma tau, ∀ x,
        (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤ J1) →
      ∀ s ∈ Icc sigma tau, ∀ t ∈ Icc sigma tau, ∀ x : ℝ,
        ‖e (c x s) - e (c x t)‖ ≤ C * |s - t| ∧
        ‖deriv (fun y => e (c y s)) x - deriv (fun y => e (c y t)) x‖ ≤
          C * |s - t| := by
  obtain ⟨E1, E2, _E3, ⟨hE1, hE2, _hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let C := max (E1 * kappa) (V * (E1 * J1 + E2 * kappa))
  have hC : 0 ≤ C := (mul_nonneg hV
    (add_nonneg (mul_nonneg hE1 hJ1) (mul_nonneg hE2 hkappa))).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro c hc sigma tau has hst htb hk hv hj s hs t ht x
  by_cases hlt : sigma < tau
  · have hclosed (r : ℝ) (hr : r ∈ Icc sigma tau) : r ∈ Icc a b :=
      ⟨has.trans hr.1, hr.2.trans htb⟩
    have hinter (r : ℝ) (hr : r ∈ Ioo sigma tau) : r ∈ Ioo a b :=
      ⟨has.trans_lt hr.1, hr.2.trans_le htb⟩
    have hdata := c2ShrinkingCurve_embedded_closed_data (m63C2_of_m62 hc) he
    have hequation (r : ℝ) (hr : r ∈ Ioo a b) (y : ℝ) :
        HasDerivAt (fun z => e (c y z))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r) (m62CurvatureVector F c r y) : W) r :=
      (c2ShrinkingCurve_embedded_interior_equation (m63C2_of_m62 hc) he).2
        r (by simpa only [interior_Icc] using hr) y
    let R : ℝ × ℝ → W := fun z => e (c z.1 z.2)
    have hR : ContDiffOn ℝ ∞ R (univ ×ˢ Ioo a b) :=
      (he.comp_contMDiffOn hc.joint_smooth).contDiffOn
    have hpartial (r : ℝ) (hr : r ∈ Ioo a b) :
        HasDerivAt (fun z => deriv (fun y => e (c y z)) x)
          (curveSpeed F c r x •
            (HAdd.hAdd (α := W) (β := W) (γ := W)
              (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r) (m63CurvatureJet F c 1 r x))
              (coordinateHessian (F.connection r) e (c x r)
                (spatialUnitTangent F c r x) (m62CurvatureVector F c r x)))) r := by
      obtain ⟨q, htime, hspace⟩ := M08.coordinate_mixed_hasDerivAt
        (isOpen_univ.prod isOpen_Ioo) R hR (p := (x, r)) ⟨mem_univ _, hr⟩
      have heq : (fun y => deriv (fun z => R (y, z)) r) =
          (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y r)
            (m62CurvatureVector F c r y) : W)) := by
        funext y
        exact (hequation r hr y).deriv
      rw [heq] at hspace
      have hvalue := hspace.unique (hasDerivAt_embeddedCurvature_spatial F c hc he hr x)
      exact htime.congr_deriv hvalue
    have hzero (r : ℝ) (hr : r ∈ Ioo sigma tau) :
        DifferentiableAt ℝ (fun z => e (c x z)) r ∧
          ‖deriv (fun z => e (c x z)) r‖ ≤ C := by
      have hd := hequation r (hinter r hr) x
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv]
      exact ((hE r (Ioo_subset_Icc_self (hinter r hr)) (c x r)
        (m62CurvatureVector F c r x) 0 0).1.trans
        (mul_le_mul_of_nonneg_left (hk r hr x) hE1)).trans (le_max_left _ _)
    have hfirst (r : ℝ) (hr : r ∈ Ioo sigma tau) :
        DifferentiableAt ℝ (fun z => deriv (fun y => e (c y z)) x) r ∧
          ‖deriv (fun z => deriv (fun y => e (c y z)) x) r‖ ≤ C := by
      have hr' := hinter r hr
      have hrc := Ioo_subset_Icc_self hr'
      have hd := hpartial r hr'
      let de : TangentSpace (𝓡 n) (c x r) →L[ℝ] W :=
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r)
      let B : W := coordinateHessian (F.connection r) e (c x r)
        (spatialUnitTangent F c r x) (m62CurvatureVector F c r x)
      have hde : ‖de (m63CurvatureJet F c 1 r x)‖ ≤ E1 * J1 :=
        ((hE r hrc (c x r) (m63CurvatureJet F c 1 r x) 0 0).1).trans
          (mul_le_mul_of_nonneg_left (hj r hr x) hE1)
      have hB : ‖B‖ ≤ E2 * kappa := by
        have hb := (hE r hrc (c x r) (spatialUnitTangent F c r x)
          (m62CurvatureVector F c r x) 0).2.1
        rw [unitTangent_norm F c hc hrc x, mul_one] at hb
        exact hb.trans (mul_le_mul_of_nonneg_left (hk r hr x) hE2)
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv]
      change ‖curveSpeed F c r x • (de (m63CurvatureJet F c 1 r x) + B)‖ ≤ C
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (speed_nonneg F c r x)]
      calc
        _ ≤ curveSpeed F c r x * (E1 * J1 + E2 * kappa) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hde hB))
            (speed_nonneg F c r x)
        _ ≤ V * (E1 * J1 + E2 * kappa) :=
          mul_le_mul_of_nonneg_right (hv r hr x) (by positivity)
        _ ≤ C := le_max_right _ _
    have hfinish (f : ℝ → W) (hf : ContinuousOn f (Icc sigma tau))
        (hd : ∀ r ∈ Ioo sigma tau, DifferentiableAt ℝ f r ∧ ‖deriv f r‖ ≤ C) :
        ‖f s - f t‖ ≤ C * |s - t| := by
      have hopen : LipschitzOnWith ⟨C, hC⟩ f (Ioo sigma tau) :=
        (convex_Ioo sigma tau).lipschitzOnWith_of_nnnorm_deriv_le
          (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2)
      have hcont : ContinuousOn f (closure (Ioo sigma tau)) := by
        simpa only [closure_Ioo hlt.ne] using hf
      have hclosure : LipschitzOnWith ⟨C, hC⟩ f (Icc sigma tau) := by
        simpa only [closure_Ioo hlt.ne] using LipschitzOnWith.closure hcont hopen
      simpa only [dist_eq_norm, Real.norm_eq_abs] using! hclosure.dist_le_mul s hs t ht
    refine ⟨hfinish (fun r => e (c x r)) ?_ hzero,
      hfinish (fun r => deriv (fun y => e (c y r)) x) ?_ hfirst⟩
    · exact hdata.2.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨mem_univ _, hclosed r hr⟩)
    · exact hdata.2.2.2.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨mem_univ _, hclosed r hr⟩)
  · have heq : sigma = tau := le_antisymm hst (le_of_not_gt hlt)
    have hsame : s = t := by
      rw [heq] at hs ht
      exact (le_antisymm hs.2 hs.1).trans (le_antisymm ht.2 ht.1).symm
    subst t
    simp

end PoincareConjecture.M63
