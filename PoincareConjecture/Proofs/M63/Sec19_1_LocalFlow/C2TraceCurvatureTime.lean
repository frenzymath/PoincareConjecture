import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureError
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedCalculus
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TracePeriodicCurvature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.ENNReal.Lemmas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem embeddedCurvature_time_derivative_bound
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    {E1 E2 : ℝ} (hE1 : 0 ≤ E1) (_hE2 : 0 ≤ E2)
    (hde : ∀ V : TangentSpace (𝓡 n) (c x t),
      Norm.norm (E := W) (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) V) ≤
        E1 * (F.metric t).tangentNorm (c x t) V)
    (hE : ∀ V Y : TangentSpace (𝓡 n) (c x t),
      ‖coordinateHessian (F.connection t) e (c x t) V Y‖ ≤
        E2 * (F.metric t).tangentNorm (c x t) V * (F.metric t).tangentNorm (c x t) Y) :
    let H := m62CurvatureVector F c t x
    let DtH := rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
      (fun r => m62CurvatureVector F c r x) t
    let B : W := HAdd.hAdd (α := W) (β := W) (γ := W)
      (coordinateHessian (F.connection t) e (c x t) H H)
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) DtH)
    HasDerivAt (fun r => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r)
      (m62CurvatureVector F c r x) : W)) B t ∧
      ‖B‖ ≤ E2 * m62Curvature F c t x ^ 2 +
        E1 * ((F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 2 t x) +
          2 * m62Curvature F c t x ^ 3 + (K0 + 4 * K2) * m62Curvature F c t x +
          4 * K1 + 2 * m62Curvature F c t x *
            (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x)) := by
  dsimp only
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let H := m62CurvatureVector F c t x
  let H2 := m63CurvatureJet F c 2 t x
  let DtH := rampHorizontalCovariantDerivative D (fun r => c x r)
    (fun r => m62CurvatureVector F c r x) t
  let de : TangentSpace (𝓡 n) p →L[ℝ] W := mfderiv (𝓡 n) 𝓘(ℝ, W) e p
  let k := m62Curvature F c t x
  let u1 := g.tangentNorm p (m63CurvatureJet F c 1 t x)
  let u2 := g.tangentNorm p H2
  let Q := 2 * k ^ 3 + (K0 + 4 * K2) * k + 4 * K1 + 2 * k * u1
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have htime : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun r : ℝ => (x, r)) t :=
    (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r => c x r) t :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp t htime
  have hHtime := (((curvatureJet_joint_contMDiff F c hc 0).contMDiffAt
    (hopen.mem_nhds hmem)).comp t htime).mdifferentiableAt (by simp)
  have hd := hasDerivAt_embedding_pushforward D he hcurve
    (fun r => m62CurvatureVector F c r x) hHtime
  rw [hc.equation t ht x] at hd
  refine ⟨hd, ?_⟩
  have hQ : g.tangentNorm p (DtH - H2) ≤ Q :=
    curvatureVector_diffusionError_norm_le F c hc h0 h1 h2 hBounds ht x
  have hnorm : g.tangentNorm p DtH ≤ u2 + Q := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    have htri := norm_add_le (DtH - H2) H2
    rw [sub_add_cancel, hn, hn, hn] at htri
    change g.tangentNorm p DtH ≤ u2 + Q
    change g.tangentNorm p (DtH - H2) ≤ Q at hQ
    change g.tangentNorm p DtH ≤ g.tangentNorm p (DtH - H2) + u2 at htri
    linarith only [htri, hQ]
  change ‖coordinateHessian D e p H H + de DtH‖ ≤
      E2 * k ^ 2 + E1 * (u2 + 2 * k ^ 3 + (K0 + 4 * K2) * k + 4 * K1 + 2 * k * u1)
  calc
    _ ≤ ‖coordinateHessian D e p H H‖ + ‖de DtH‖ := norm_add_le _ _
    _ ≤ E2 * k * k + E1 * (u2 + Q) :=
      add_le_add (hE H H) ((hde DtH).trans (mul_le_mul_of_nonneg_left hnorm hE1))
    _ = _ := by dsimp only [Q]; ring




theorem exists_uniform_embeddedCurvature_time_lipschitz
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M)) (hab : a < b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {kappa J1 J2 : ℝ} (hkappa : 0 ≤ kappa) (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) :
    ∃ C ≥ 0, ∀ (c : ℝ → ℝ → M), M62ShrinkingCurve F c →
      ∀ (sigma tau : ℝ), a ≤ sigma → sigma ≤ tau → tau ≤ b →
      (∀ r ∈ Ioo sigma tau, ∀ x : ℝ, m62Curvature F c r x ≤ kappa) →
      (∀ r ∈ Ioo sigma tau, ∀ x : ℝ,
        (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤ J1) →
      (∀ r ∈ Ioo sigma tau, ∀ x : ℝ,
        (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 2 r x) ≤ J2) →
      ∀ s ∈ Icc sigma tau, ∀ t ∈ Icc sigma tau, ∀ x : ℝ,
        ‖HSub.hSub (α := W) (β := W) (γ := W)
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x s) (m62CurvatureVector F c s x))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x))‖ ≤ C * |s - t| := by
  obtain ⟨E1, E2, _E3, ⟨hE1, hE2, _hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let C := E2 * kappa ^ 2 +
    E1 * (J2 + 2 * kappa ^ 3 + (K0 + 4 * K2) * kappa + 4 * K1 + 2 * kappa * J1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c hc sigma tau has hst htb hk hu hw s hs t ht x
  let H : ℝ → W := fun r =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x r) (m62CurvatureVector F c r x)
  by_cases hlt : sigma < tau
  · have hder (r : ℝ) (hr : r ∈ Ioo sigma tau) :
        DifferentiableAt ℝ H r ∧ ‖deriv H r‖ ≤ C := by
      have hr' : r ∈ Ioo a b := ⟨has.trans_lt hr.1, hr.2.trans_le htb⟩
      have hrclosed := Ioo_subset_Icc_self hr'
      obtain ⟨hd, hb⟩ := embeddedCurvature_time_derivative_bound F c hc he
        h0 h1 h2 hBounds hr' x hE1 hE2
        (fun V => (hE r hrclosed (c x r) V 0 0).1)
        (fun V Y => (hE r hrclosed (c x r) V Y 0).2.1)
      refine ⟨hd.differentiableAt, ?_⟩
      change ‖deriv (fun z => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x z)
        (m62CurvatureVector F c z x) : W)) r‖ ≤ C
      rw [hd.deriv]
      apply hb.trans
      have hkr := hk r hr x
      have hur := hu r hr x
      have hwr := hw r hr x
      have hk0 := curvature_nonneg F c r x
      have hu0 : 0 ≤ (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) :=
        Real.sqrt_nonneg _
      dsimp only [C]
      gcongr
    have hclosed : ContinuousOn H (Icc sigma tau) :=
      ((embeddedCurvature_closed_periodic_data F c hab hc he).2.1).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun r hr => ⟨mem_univ _, ⟨has.trans hr.1, hr.2.trans htb⟩⟩)
    have hopen : LipschitzOnWith ⟨C, hC⟩ H (Ioo sigma tau) :=
      (convex_Ioo sigma tau).lipschitzOnWith_of_nnnorm_deriv_le
        (fun r hr => (hder r hr).1) (fun r hr => (hder r hr).2)
    have hclosure : LipschitzOnWith ⟨C, hC⟩ H (Icc sigma tau) := by
      have hcont : ContinuousOn H (closure (Ioo sigma tau)) := by
        simpa only [closure_Ioo hlt.ne] using hclosed
      simpa only [closure_Ioo hlt.ne] using LipschitzOnWith.closure hcont hopen
    simpa only [dist_eq_norm, Real.norm_eq_abs] using! hclosure.dist_le_mul s hs t ht
  · have heq : sigma = tau := le_antisymm hst (le_of_not_gt hlt)
    have hsame : s = t := by
      rw [heq] at hs ht
      exact (le_antisymm hs.2 hs.1).trans (le_antisymm ht.2 ht.1).symm
    subst t
    simp

end PoincareConjecture.M63
