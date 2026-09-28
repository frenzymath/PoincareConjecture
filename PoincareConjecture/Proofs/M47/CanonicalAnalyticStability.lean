import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import PoincareConjecture.Proofs.M47.PositiveGradientEvolution
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientNorm
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem continuous_scalarEvolution_timeSubtype (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) :
    Continuous (fun z : J × M =>
      (F.connection z.1.val).laplacian (F.connection z.1.val).scalarCurvature z.2 +
        2 * (F.connection z.1.val).ricciNormSq z.2) := by
  have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hL := M04.continuousOn_flow_timeDependentLaplacian F
    (hC.scalar_regular 3 M J F)
  have hE := hL.add ((M04.continuousOn_flow_ricciNormSq F).const_mul 2)
  have h := hE.comp_continuous hmap (fun z => ⟨z.1.property, mem_univ z.2⟩)
  exact h



theorem continuous_scalarGradientNorm_timeSubtype (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) :
    Continuous (fun z : J × M =>
      scalarGradientNorm (F.metric z.1.val) (F.connection z.1.val) z.2) := by
  have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hG := (M47Positive.continuousOn_scalar_gradient_energy hC F).comp_continuous
    hmap (fun z => ⟨z.1.property, mem_univ z.2⟩)
  simpa only [scalarGradientNorm_eq_tangentNorm, RiemannianMetric.tangentNorm,
    Function.comp_apply]
    using hG.sqrt

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]

private theorem cap_bound_persists (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) (t : J)
    (N : CapCertificate (F.metric t.val)) (hconnection : N.connection = F.connection t.val)
    (A : J × M → ℝ) (hA : Continuous A) (p : ℝ) (hp : 0 ≤ p)
    (hbound : ∃ b : ℝ, b < N.cap_constant ∧ ∀ x ∈ N.carrier,
      A (t, x) ≤ b * (F.connection t.val).scalarCurvature x ^ p) :
    ∃ b' : ℝ, b' < N.cap_constant ∧ ∀ᶠ s : J in 𝓝 t,
      ∀ x ∈ N.carrier, A (s, x) ≤ b' * (F.connection s.val).scalarCurvature x ^ p := by
  obtain ⟨m, hm, _, _, _, hfloor, _⟩ := cap_uniform_scalar_lower N
  rw [hconnection] at hfloor
  obtain ⟨b, hb, hbound⟩ := hbound
  let b' := (b + N.cap_constant) / 2
  have hb'C : b' < N.cap_constant := by dsimp only [b']; linarith
  have hgap : 0 < b' - b := by dsimp only [b']; linarith
  let c := (b' - b) * m ^ p
  have hc : 0 < c := mul_pos hgap (Real.rpow_pos_of_pos hm p)
  have hmap : Continuous (fun z : J × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hR := (hC.scalar_regular 3 M J F).continuousOn.comp_continuous
    hmap (fun z => ⟨z.1.property, mem_univ z.2⟩)
  let G : J × M → ℝ := fun z => b' * (F.connection z.1.val).scalarCurvature z.2 ^ p - A z
  have hG : Continuous G := (continuous_const.mul
    (hR.rpow_const (fun _ => Or.inr hp))).sub hA
  have hbase := hG.comp (continuous_const.prodMk continuous_snd :
    Continuous (fun z : J × M => (t, z.2)))
  have hdiff := (hG.sub hbase).abs
  have hnear : ∀ᶠ s : J in 𝓝 t, ∀ x ∈ (univ : Set M),
      |G (s, x) - G (t, x)| < c / 2 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro x _
    exact hdiff.continuousAt.eventually (Iio_mem_nhds (by
      change |G (t, x) - G (t, x)| < c / 2
      simpa only [sub_self, abs_zero] using half_pos hc))
  refine ⟨b', hb'C, ?_⟩
  filter_upwards [hnear] with s hs x hx
  have hpower := Real.rpow_le_rpow hm.le (hfloor x hx) hp
  have hscaled := mul_le_mul_of_nonneg_left hpower hgap.le
  have hold := hbound x hx
  have hmargin : c ≤ G (t, x) := by
    dsimp only [c, G]
    nlinarith
  have hchange := (abs_lt.mp (hs x (mem_univ x))).1
  change A (s, x) ≤ b' * (F.connection s.val).scalarCurvature x ^ p
  dsimp only [G] at hmargin hchange
  linarith



theorem cap_gradient_bound_persists (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) (t : J)
    (N : CapCertificate (F.metric t.val)) (hconnection : N.connection = F.connection t.val) :
    ∃ b' : ℝ, b' < N.cap_constant ∧ ∀ᶠ s : J in 𝓝 t,
      ∀ x ∈ N.carrier,
        scalarGradientNorm (F.metric s.val) (F.connection s.val) x ≤
          b' * (F.connection s.val).scalarCurvature x ^ (3 / 2 : ℝ) := by
  apply cap_bound_persists hC F t N hconnection
    (fun z => scalarGradientNorm (F.metric z.1.val) (F.connection z.1.val) z.2)
    (continuous_scalarGradientNorm_timeSubtype hC F) (3 / 2) (by norm_num)
  simpa only [hconnection] using N.gradient_bound



theorem cap_evolution_bound_persists (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) (t : J)
    (N : CapCertificate (F.metric t.val)) (hconnection : N.connection = F.connection t.val) :
    ∃ b' : ℝ, b' < N.cap_constant ∧ ∀ᶠ s : J in 𝓝 t,
      ∀ x ∈ N.carrier,
        |(F.connection s.val).laplacian (F.connection s.val).scalarCurvature x +
          2 * (F.connection s.val).ricciNormSq x| ≤
          b' * (F.connection s.val).scalarCurvature x ^ 2 := by
  have h := cap_bound_persists hC F t N hconnection
    (fun z => |(F.connection z.1.val).laplacian (F.connection z.1.val).scalarCurvature z.2 +
      2 * (F.connection z.1.val).ricciNormSq z.2|)
    (continuous_scalarEvolution_timeSubtype hC F).abs 2 (by norm_num) (by
      simpa only [hconnection, Real.rpow_two] using N.laplacian_bound)
  simpa only [Real.rpow_two] using h

end PoincareConjecture.Proofs.M47
