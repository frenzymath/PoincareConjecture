import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PrescribedNormalApproximationSlab
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonNormalCurvatureBounds
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SliceCongruence
import Mathlib.Data.Countable.Defs











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {I : Type w} [Countable I] [Nonempty I]
  {a b L T : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem exists_countable_normal_pool_common_slab
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (hL : 0 < L) (hT : 0 < T) (hT1 : T ≤ 1) (hTb : a + T ≤ b)
    (q : I → ℝ → ℝ → W)
    (hq : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (q i)) (Icc 0 T ×ˢ univ))
    (hper : ∀ i, ∀ t ∈ Icc 0 T, Function.Periodic (q i t) L)
    (hguard : ∀ i, ∀ t ∈ Icc 0 T, ∀ x, q i t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q i t x) (deriv (q i t) x) ≠ 0)
    (hfixed : ∀ i, ∀ t ∈ Icc 0 T, ∀ x, q i t x = e (ρ (q i t x)))
    (htime : ∀ i, ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => q i s x)
      (ambientCurvePrincipal F ρ (a + t) (q i t x) (deriv (q i t) x) •
          deriv (deriv (q i t)) x +
        ambientCurveLower F e ρ (a + t) (q i t x) (deriv (q i t) x)) t)
    (m : I → ℝ) (hm : ∀ i, (1 / 2 : ℝ) ≤ m i ∧ m i ≤ 3 / 2)
    (hspeed : ∀ i x, curveSpeed F (fun y _ => ρ (q i 0 y)) a x = m i)
    {R0 : ℝ} (hR0 : 0 ≤ R0)
    (hinit : ∀ i x, m62CurvatureSquared F
      (fun y (_ : ℝ) => ρ (q i 0 ((L / curvePeriod) * y))) a x ≤ R0) :
    let κ := L / curvePeriod
    let A := fun i t x =>
      ambientCurvePrincipal F ρ (a + t) (q i t x) (deriv (q i t) x)
    ∃ ψ : I → ℝ → ℝ → ℝ,
      let c := fun i x t => ρ (q i (t - a) (ψ i (t - a) (κ * x)))
      (∀ i,
        (∀ x, ψ i 0 x = x) ∧
        (∀ t ∈ Icc 0 (T / 4), ∀ x, ψ i t (x + L) = ψ i t x + L) ∧
        ContDiffOn ℝ ∞ (Function.uncurry (ψ i)) (Icc 0 (T / 4) ×ˢ univ) ∧
        (∀ t ∈ Icc 0 (T / 4), ∀ x, HasDerivWithinAt (fun s => ψ i s x)
          (deriv (A i t) (ψ i t x) / 2) (Icc 0 (T / 4)) t) ∧
        (∀ t ∈ Icc 0 (T / 4), ∀ x, 0 < deriv (ψ i t) x) ∧
        (∀ t ∈ Icc 0 (T / 4), Function.Bijective (ψ i t)) ∧
        M63SmoothShrinkingCurveOn F (c i) (Icc a (a + T / 4)) ∧
        (∀ x, c i x a = ρ (q i 0 (κ * x))) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
          (fun z : ℝ × ℝ => c i z.1 z.2) (univ ×ˢ Icc a (a + T / 4))) ∧
      (∀ i x, curveSpeed F (c i) a x = κ * m i) ∧
      (∀ i x, κ / 2 ≤ curveSpeed F (c i) a x ∧
        curveSpeed F (c i) a x ≤ 3 * κ / 2) ∧
      ∃ delta : ℝ, 0 < delta ∧ a + 2 * delta ≤ a + T / 4 ∧
        a + 2 * delta < b ∧ 2 * delta ≤ 1 ∧
        ∃ R J : ℝ, 0 ≤ R ∧ 0 ≤ J ∧
          (∀ i, ∀ t ∈ Icc a (a + 2 * delta), ∀ x,
            m62CurvatureSquared F (c i) t x ≤ R) ∧
          (∀ i, ∀ t ∈ Ioo a (a + 2 * delta), ∀ x,
            (F.metric t).tangentNorm (c i x t)
              (m63CurvatureJet F (c i) 1 t x) ≤ J / Real.sqrt (t - a)) := by
  classical
  dsimp only
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos hL Real.two_pi_pos
  have hS : 0 < T / 4 := by positivity
  have hS1 : T / 4 ≤ 1 / 2 := by linarith only [hT1]
  have hlabels (i : I) := exists_normal_curve_on_prescribed_ambient_slab
    F he hU heU hρ hρe hL hT hS hTb le_rfl hS1
      (hq i) (hper i) (hguard i) (hfixed i) (htime i)
  choose ψ hψzero hψper hψjoint hψode hψpos hψbij hc hc0 hcjoint using hlabels
  let c : I → ℝ → ℝ → M := fun i x t => ρ (q i (t - a) (ψ i (t - a) (κ * x)))
  have hqslice (i : I) : ContDiff ℝ ∞ (q i 0) := by
    have hmap : ContDiff ℝ ∞ (fun x : ℝ => ((0 : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    exact (hq i).comp_contDiff hmap (fun _ => ⟨⟨le_rfl, hT.le⟩, mem_univ _⟩)
  have hspatial (i : I) : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun x => ρ (q i 0 x)) := by
    intro x
    exact ((hρ.contMDiffAt (hU.mem_nhds (hguard i 0 ⟨le_rfl, hT.le⟩ x).1)).mdifferentiableAt
      (by simp)).comp x ((hqslice i).contMDiff.mdifferentiable (by simp) x)
  have hspeedc (i : I) (x : ℝ) : curveSpeed F (c i) a x = κ * m i := by
    calc
      _ = curveSpeed F (fun y (_ : ℝ) => ρ (q i 0 (κ * y))) a x :=
        curveSpeed_congr_slice F (hc0 i)
      _ = κ * curveSpeed F (fun y (_ : ℝ) => ρ (q i 0 y)) a (κ * x) :=
        curveSpeed_comp F (fun y (_ : ℝ) => ρ (q i 0 y)) (t := a) (x := x)
          (hspatial i _) (by
          simpa only [mul_one, id_eq] using (hasDerivAt_id x).const_mul κ) hκ.le
      _ = κ * m i := congrArg (κ * ·) (hspeed i _)
  have hsband (i : I) (x : ℝ) :
      κ / 2 ≤ curveSpeed F (c i) a x ∧ curveSpeed F (c i) a x ≤ 3 * κ / 2 := by
    rw [hspeedc]
    have hlo := mul_le_mul_of_nonneg_left (hm i).1 hκ.le
    have hhi := mul_le_mul_of_nonneg_left (hm i).2 hκ.le
    constructor <;> linarith only [hlo, hhi]
  have hSbelow : a + T / 4 < b := by linarith only [hT, hTb]
  obtain ⟨en, hen⟩ := exists_surjective_nat I
  have hinitial (j : ℕ) (x : ℝ) : m62CurvatureSquared F (c (en j)) a x ≤ R0 := by
    rw [curvatureSquared_congr_slice F
      (d := fun y (_ : ℝ) => ρ (q (en j) 0 (κ * y))) (hc0 (en j))]
    exact hinit (en j) x
  obtain ⟨delta, hdelta, hdeltaT, hone, R, _J, hR, _hJ, hcapn, _hjetn⟩ :=
    exists_common_normal_curvature_bounds F hcompact
      (by linarith only [hS] : a < a + T / 4) hSbelow.le
      (fun j => c (en j)) (fun j => hc (en j)) hR0 hinitial
  have hcap (i : I) (t : ℝ) (ht : t ∈ Icc a (a + 2 * delta)) (x : ℝ) :
      m62CurvatureSquared F (c i) t x ≤ R := by
    obtain ⟨j, rfl⟩ := hen i
    exact hcapn j t ht x
  have haD : a < a + 2 * delta := by linarith only [hdelta]
  have hDb : a + 2 * delta < b := hdeltaT.trans_lt hSbelow
  have hsub : Icc a (a + 2 * delta) ⊆ Icc a (a + T / 4) :=
    Icc_subset_Icc_right hdeltaT
  have hsubF : Icc a (a + 2 * delta) ⊆ Icc a b := Icc_subset_Icc_right hDb.le
  let Fwide := m63RestrictClosedFlow F a (a + 2 * delta) hsubF haD
  have hcwide (i : I) : M62ShrinkingCurve Fwide (c i) :=
    m63SmoothRestriction (hc i) a (a + 2 * delta) hsub haD
  obtain ⟨C0, hC0, hjet⟩ := m63Exists_boundedCurvature_firstJet_bound Fwide hcompact hR
  refine ⟨ψ, fun i => ⟨hψzero i, hψper i, hψjoint i, hψode i,
    hψpos i, hψbij i, hc i, hc0 i, hcjoint i⟩, hspeedc, hsband,
    delta, hdelta, hdeltaT, hDb, hone, R, Real.sqrt C0, hR, Real.sqrt_nonneg _, hcap, ?_⟩
  intro i t ht x
  have hage : t - a ≤ 1 := by linarith only [ht.2, hone]
  have hbound := hjet (c i) (hcwide i)
    (fun s hs y => hcap i s (Ioo_subset_Icc_self hs) y) x t ht hage
  change Real.sqrt (m63CurvatureJetSquared Fwide (c i) 1 t x) ≤
    Real.sqrt C0 / Real.sqrt (t - a)
  exact (Real.sqrt_le_sqrt hbound).trans_eq (Real.sqrt_div hC0 _)

end PoincareConjecture.M63
