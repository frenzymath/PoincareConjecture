import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Weak











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

omit [MeasurableSpace M] [BorelSpace M] in
private lemma exists_spatial_cutoff_extension
    (g : RiemannianMetric n M)
    {F : ℝ × M → ℝ} {Ω K : Set M} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ Ω)) :
    ∃ G : ℝ × M → ℝ,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ G (Ioi 0 ×ˢ univ) ∧
      (∀ t x, x ∈ K → G (t, x) = F (t, x)) ∧
      (∀ t x, x ∈ K → (fun y => G (t, y)) =ᶠ[𝓝 x] (fun y => F (t, y))) := by
  obtain ⟨E⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨E, E.isCompact, E.iUnion_eq⟩
  obtain ⟨χ, hχzero, hχone, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (n := ⊤) (𝓡 n) hΩ.isClosed_compl hK.isClosed (disjoint_compl_left_iff.mpr hKΩ)
  have hχK (x : M) (hx : x ∈ K) : (χ : M → ℝ) =ᶠ[𝓝 x] 1 :=
    hχone.filter_mono (nhds_le_nhdsSet hx)
  have hχΩ : tsupport (χ : M → ℝ) ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (hχzero.filter_mono (nhds_le_nhdsSet hxΩ))) hx
  refine ⟨fun p => χ p.2 * F p, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hx : p.2 ∈ Ω
    · exact (((χ.contMDiff p.2).comp p contMDiffAt_snd).mul
        (hF.contMDiffAt ((isOpen_Ioi.prod hΩ).mem_nhds ⟨hp.1, hx⟩))).contMDiffWithinAt
    · have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχΩ h))
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [continuousAt_snd.eventually hz] with q hq
      simp [hq]
  · intro t x hx
    change χ x * F (t, x) = F (t, x)
    simp only [(hχK x hx).self_of_nhds, Pi.one_apply, one_mul]
  · intro t x hx
    filter_upwards [hχK x hx] with y hy
    simp [hy]



theorem hasDerivAt_integral_test_mul_of_heatEquationOn
    (D : LeviCivitaData g) {F : ℝ × M → ℝ} {Ω : Set M} (hΩ : IsOpen Ω)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ Ω))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω)
    {t : ℝ} (ht : 0 < t)
    (hheat : ∀ x ∈ tsupport φ, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t) :
    HasDerivAt (fun s => ∫ x, φ x * F (s, x) ∂g.volumeMeasure)
      (∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure) t := by
  obtain ⟨G, hG, hGF, hgerm⟩ := exists_spatial_cutoff_extension (g := g) hΩ
    hφc.isCompact hφΩ hF
  have hheatG (x : M) (hx : x ∈ tsupport φ) :
      HasDerivAt (fun s => G (s, x)) (D.laplacian (fun y => G (t, y)) x) t := by
    rw [D.laplacian_eq_of_eventuallyEq (hgerm t x hx)]
    simpa only [hGF _ x hx] using hheat x hx
  have h := D.hasDerivAt_integral_test_mul_of_heatEquation_on_tsupport hG hφ hφc ht hheatG
  have hpair (s : ℝ) : (∫ x, φ x * G (s, x) ∂g.volumeMeasure) =
      ∫ x, φ x * F (s, x) ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [hGF _ x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hlap : (∫ x, G (t, x) * D.laplacian φ x ∂g.volumeMeasure) =
      ∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [hGF _ x hx]
    · simp [D.laplacian_eq_zero_of_notMem_tsupport hx]
  simpa only [hpair, hlap] using h

end PoincareConjecture.LeviCivitaData
