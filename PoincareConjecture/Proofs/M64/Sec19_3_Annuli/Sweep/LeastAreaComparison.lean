import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.SweptArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoinArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.MetricAreaComparison
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflection













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in
private theorem leastArea_affine_comparison
    {g h : RiemannianMetric n M} {c0 c1 d0 d1 : ℝ → M}
    (A : M64Annulus g c0 c1) {k E : ℝ} (hk : 0 < k)
    (hcomp : ∀ B : M64Annulus g c0 c1,
      ∃ D : M64Annulus h d0 d1, D.area ≤ k * B.area + E) :
    m64LeastAnnulusArea h d0 d1 ≤ k * m64LeastAnnulusArea g c0 c1 + E := by
  have hnonempty := m64AnnulusAreaRange_nonempty A
  have _hbounded := m64AnnulusAreaRange_bddBelow g c0 c1
  have h : (m64LeastAnnulusArea h d0 d1 - E) / k ≤ m64LeastAnnulusArea g c0 c1 := by
    apply le_csInf hnonempty
    rintro _ ⟨B, rfl⟩
    obtain ⟨D, hD⟩ := hcomp B
    apply (div_le_iff₀ hk).mpr
    have hle := (m64LeastAnnulusArea_le_annulus D).trans hD
    nlinarith
  have hle := (div_le_iff₀ hk).mp h
  nlinarith




theorem m64LeastAnnulusArea_two_sided_local
    {a b : ℝ} {F : RicciFlow n M (Icc a b)}
    (hcompact : IsCompact (univ : Set M))
    {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {s : ℝ} (hs : s ∈ Icc a b)
    (A : M64Annulus (F.metric s) (fun x => c0 x s) (fun x => c1 x s)) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ t ∈ Icc a b,
      m64LeastAnnulusArea (F.metric t) (fun x => c0 x t) (fun x => c1 x t) ≤
        Real.exp ((n : ℝ) * K * |t - s|) ^ 2 *
          (m64LeastAnnulusArea (F.metric s) (fun x => c0 x s) (fun x => c1 x s) +
            C * |t - s|) ∧
      m64LeastAnnulusArea (F.metric s) (fun x => c0 x s) (fun x => c1 x s) ≤
        Real.exp ((n : ℝ) * K * |t - s|) ^ 2 *
          m64LeastAnnulusArea (F.metric t) (fun x => c0 x t) (fun x => c1 x t) +
            C * |t - s| := by
  obtain ⟨K, hK, hcurv⟩ := m64_compact_flow_curvature_bound F hcompact
  obtain ⟨C0, hC0, hS0⟩ := m64Annulus_of_c2_sweep_area hc0 (F.metric s)
  obtain ⟨C1, hC1, hS1⟩ := m64Annulus_of_c2_sweep_area hc1 (F.metric s)
  refine ⟨K, C0 + C1, hK, add_nonneg hC0 hC1, ?_⟩
  intro t ht
  let k := Real.exp ((n : ℝ) * K * |t - s|) ^ 2
  have hk : 0 < k := sq_pos_of_pos (Real.exp_pos _)
  let E := (C0 + C1) * |t - s|
  obtain ⟨S0, _hmap0, hs0⟩ := hS0 t ht s hs
  obtain ⟨S1, _hmap1, hs1⟩ := hS1 s hs t ht
  have hs0' : S0.area ≤ C0 * |t - s| := by
    simpa only [abs_sub_comm s t] using hs0
  have hforward (B : M64Annulus (F.metric s)
      (fun x => c0 x s) (fun x => c1 x s)) :
      ∃ D : M64Annulus (F.metric t) (fun x => c0 x t) (fun x => c1 x t),
        D.area ≤ k * B.area + k * E := by
    obtain ⟨C, _hCmap, hCarea⟩ := m64Annulus_join_with_area S0 B
    obtain ⟨D, _hDmap, hDarea⟩ := m64Annulus_join_with_area C S1
    have hD : D.area ≤ B.area + E := by
      rw [hDarea, hCarea]
      dsimp only [E]
      nlinarith
    obtain ⟨T, _hTmap, hTarea⟩ := m64Annulus_transport_time_area F hK hcurv hs ht D
    refine ⟨T, ?_⟩
    calc
      T.area ≤ k * D.area := hTarea
      _ ≤ k * (B.area + E) := mul_le_mul_of_nonneg_left hD hk.le
      _ = _ := mul_add _ _ _
  obtain ⟨At, _hAtarea⟩ := hforward A
  have hbackward (B : M64Annulus (F.metric t)
      (fun x => c0 x t) (fun x => c1 x t)) :
      ∃ D : M64Annulus (F.metric s) (fun x => c0 x s) (fun x => c1 x s),
        D.area ≤ k * B.area + E := by
    obtain ⟨T, _hTmap, hTarea⟩ := m64Annulus_transport_time_area F hK hcurv ht hs B
    have hT : T.area ≤ k * B.area := by
      simpa only [abs_sub_comm s t] using hTarea
    obtain ⟨C, _hCmap, hCarea⟩ := m64Annulus_join_with_area (m64Annulus_reverse S0) T
    obtain ⟨D, _hDmap, hDarea⟩ := m64Annulus_join_with_area C (m64Annulus_reverse S1)
    refine ⟨D, ?_⟩
    rw [hDarea, hCarea, m64Annulus_reverse_area, m64Annulus_reverse_area]
    dsimp only [E]
    nlinarith
  constructor
  · have h := leastArea_affine_comparison A hk hforward
    simpa only [k, E, mul_add] using h
  · exact leastArea_affine_comparison At hk hbackward

end PoincareConjecture
