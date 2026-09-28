import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.LevelTransport











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open Poincare.Riemannian.Soul
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in


theorem exists_smooth_exhaustion_level_transport
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let f := busemannExhaustion p
    ∃ l : ℝ, 0 < l ∧ ∀ x₀ : M, 2 ≤ f x₀ → ∀ e : ℝ, 0 < e → e ≤ 1 / 8 →
      let C := horoballIntersection p (f x₀ + 2)
      let U := {x | 1 / 2 < f x ∧ f x < f x₀ + 1 + 1 / 2}
      ∃ (u : M → ℝ) (H : ℝ) (V : Set M) (Q : M → M),
        0 < H ∧ ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ u ∧
        (∀ x ∈ C, 0 < f x → |u x - f x| ≤ e) ∧
        (∀ x ∈ C, g.tangentNorm x (D.gradient u x) ≤ 2) ∧
        (∀ x ∈ C, ∀ v : TangentSpace (𝓡 3) x,
          -H * g.inner x v v ≤ D.hessian u x v v) ∧
        (∀ x ∈ C, 1 ≤ f x → H * (g.edist x p).toReal ≤ 2 * l ∧
          2 * l * (g.edist x p).toReal ≤ u x - u p) ∧
        1 < u x₀ ∧ u x₀ < f x₀ + 1 ∧
        (∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0) ∧
        IsCompact {x | x ∈ U ∧ u x ∈ Icc 1 (u x₀)} ∧
        IsOpen V ∧ {x | x ∈ U ∧ u x = u x₀} ⊆ V ∧ V ⊆ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q V ∧
        MapsTo Q {x | x ∈ U ∧ u x = u x₀} {x | x ∈ U ∧ u x = 1} ∧
        SurjOn Q {x | x ∈ U ∧ u x = u x₀} {x | x ∈ U ∧ u x = 1} ∧
        InjOn Q {x | x ∈ U ∧ u x = u x₀} ∧
        ∀ x ∈ U, u x = u x₀ → ∀ v : TangentSpace (𝓡 3) x,
          mvfderiv (𝓡 3) u x v = 0 →
          g.tangentNorm (Q x) (mfderiv (𝓡 3) (𝓡 3) Q x v) ≤
            2 * g.tangentNorm x v := by
  let := g.toMetricSpace
  let f := busemannExhaustion p
  obtain ⟨l, hl, hsmooth⟩ :=
    g.exists_smooth_exhaustion_approx_with_uniform_radial_gap D hc hsec p
  refine ⟨l, hl, ?_⟩
  intro x₀ hx₀ e he heighth
  let b := f x₀ + 1
  let C := horoballIntersection p (b + 1)
  let U := {x | 1 / 2 < f x ∧ f x < b + 1 / 2}
  have hb : 1 ≤ b := by dsimp [b]; linarith
  obtain ⟨lb, hlb, hU, happrox⟩ := hsmooth b hb
  let η := lb ^ 2 * Real.log 2 / b
  have hη : 0 < η := by
    apply div_pos (mul_pos (sq_pos_of_pos hlb) (Real.log_pos (by norm_num)))
    linarith
  obtain ⟨u, H, hH, hHη, hu, _, _, herror, hupper, hhess, hgrad, hband, hradial⟩ :=
    happrox e η he hη
  have hxC : x₀ ∈ C :=
    (busemannExhaustion_le_iff (by dsimp [b]; linarith : 0 ≤ b + 1)).mp (by
      change f x₀ ≤ b + 1
      dsimp [b]
      linarith)
  have herrcenter := abs_le.mp (herror x₀ hxC (by linarith))
  have hcpos : 1 < u x₀ := by linarith [herrcenter.1]
  have hcb : u x₀ < b := by dsimp [b]; linarith [herrcenter.2]
  have hUC : U ⊆ C := by
    intro x hx
    apply (busemannExhaustion_le_iff (by linarith : 0 ≤ b + 1)).mp
    change f x ≤ b + 1
    linarith [hx.2]
  have hregular (x : M) (hx : x ∈ U) : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) u x ≠ 0 := by
    intro hz
    have hg := (gradient_eq_zero_iff_mfderiv_eq_zero_manifold D u x).mpr hz
    have hlower := hgrad x hx
    simp only [hg, tangentNorm, map_zero, Real.sqrt_zero] at hlower
    exact (not_le_of_gt hlb) hlower
  have hcompact : IsCompact {x | x ∈ U ∧ u x ∈ Icc 1 (u x₀)} := by
    have heq : {x | x ∈ U ∧ u x ∈ Icc 1 (u x₀)} =
        {x | x ∈ U ∧ u x ∈ Icc 1 b} ∩ u ⁻¹' Iic (u x₀) := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc, mem_inter_iff, mem_preimage, mem_Iic]
      exact ⟨fun hx => ⟨⟨hx.1, hx.2.1, hx.2.2.trans hcb.le⟩, hx.2.2⟩,
        fun hx => ⟨hx.1.1, hx.1.2.1, hx.2⟩⟩
    rw [heq]
    exact hband.inter_right (isClosed_Iic.preimage hu.continuous)
  obtain ⟨V, Q, hV, htopV, hVU, hQ, hmaps, honto, hinj, hbound⟩ :=
    D.exists_bijective_lower_level_transport_of_hessian_ge_neg hu hU hlb hH.le hcpos.le
      hgrad (fun x hx v => hhess x (hUC hx) v) hcompact
  have hexp : Real.exp ((H / lb ^ 2) * (u x₀ - 1)) ≤ 2 := by
    apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log (by norm_num : (0 : ℝ) < 2))
    have hfactor : H / lb ^ 2 ≤ Real.log 2 / b := by
      apply (div_le_iff₀ (sq_pos_of_pos hlb)).mpr
      calc
        H ≤ η := hHη
        _ = (Real.log 2 / b) * lb ^ 2 := by dsimp [η]; ring
    calc
      (H / lb ^ 2) * (u x₀ - 1) ≤ (Real.log 2 / b) * (u x₀ - 1) :=
        mul_le_mul_of_nonneg_right hfactor (by linarith)
      _ ≤ (Real.log 2 / b) * b :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Real.log 2 := div_mul_cancel₀ _ (by linarith)
  refine ⟨u, H, V, Q, hH, hu, ?_, ?_, ?_, ?_, hcpos, hcb, hregular, hcompact,
    hV, htopV, hVU, hQ, hmaps, honto, hinj, ?_⟩
  · simpa only [b, add_assoc, one_add_one_eq_two] using herror
  · simpa only [b, add_assoc, one_add_one_eq_two] using hupper
  · simpa only [b, add_assoc, one_add_one_eq_two] using hhess
  · simpa only [b, add_assoc, one_add_one_eq_two] using hradial
  · intro x hx hlevel v hv
    exact (hbound x hx hlevel v hv).trans
      (mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _))

end PoincareConjecture.RiemannianMetric
