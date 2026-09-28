import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]


theorem exists_graph_push_family_within
    (b : E → Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b)
    {O : Set (E × Real)} (hO : IsOpen O)
    (htrace : ∀ x ∈ tsupport b, ∀ t ∈ Icc (0 : Real) 1, (x, t * b x) ∈ O) :
    ∃ K : Set (E × Real), IsCompact K ∧ K ⊆ O ∧
      ∃ Φ : Real → Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p, Φ 0 p = p) ∧
        ContDiff Real ∞ (fun z : Real × (E × Real) => Φ z.1 z.2) ∧
        (∀ t p, (Φ t p).1 = p.1) ∧
        (∀ t p, p ∉ K → Φ t p = p) ∧
        ∀ x, Φ 1 (x, 0) = (x, b x) := by
  let T : Set (E × Real) :=
    (fun p : E × Real => (p.1, p.2 * b p.1)) '' (tsupport b ×ˢ Icc 0 1)
  have hT : IsCompact T := (hbc.prod isCompact_Icc).image
    (continuous_fst.prodMk (continuous_snd.mul (hb.continuous.comp continuous_fst)))
  have hTO : T ⊆ O := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact htrace x hx t ht
  obtain ⟨K, hK, hTK, hKO⟩ := exists_compact_between hT hO hTO
  obtain ⟨chi, hchi, hchi0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E × Real)
      hT.isClosed hTK (n := ⊤)
  let V : E × Real → E × Real := fun p => (0, chi p * b p.1)
  have hV : ContDiff Real ∞ V :=
    contDiff_const.prodMk (chi.contMDiff.contDiff.mul (hb.comp contDiff_fst))
  have hVzero (p : E × Real) (hp : p ∉ K) : V p = 0 := by
    simp [V, hchi0 p hp]
  have hVline (x : E) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      V (x, t * b x) = (0, b x) := by
    by_cases hx : x ∈ tsupport b
    · have hmem : (x, t * b x) ∈ T := ⟨(x, t), ⟨hx, ht⟩, rfl⟩
      simp only [V, hchi.self_of_nhdsSet _ hmem, one_mul]
    · simp [V, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨Φ, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun p : Real × (E × Real) => V p.2) (hV.comp contDiff_snd) hK
      (fun _ p hp => hVzero p hp)
  have hfirst (s t : Real) (p : E × Real) : (Φ s t p).1 = p.1 := by
    have hd (r : Real) : HasDerivAt (fun r => (Φ s r p).1) 0 r := by
      exact (ContinuousLinearMap.fst Real E Real).hasFDerivAt.comp_hasDerivAt r
        (ho s p r)
    have he := is_const_of_deriv_eq_zero
      (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t s
    simpa only [hi] using he
  have hVc : HasCompactSupport V := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra hn
    exact hp (hVzero p hn)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hV (by simp)
  refine ⟨K, hK, hKO, Φ 0, hi 0, hs 0, hfirst 0, hfix 0, ?_⟩
  intro x
  have hd (t : Real) : HasDerivAt (fun r : Real => (x, r * b x)) (0, b x) t := by
    simpa using (hasDerivAt_const t x).prodMk ((hasDerivAt_id t).mul_const (b x))
  have he := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
    (f := fun t => Φ 0 t (x, 0)) (g := fun t : Real => (x, t * b x))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t _ => (ho 0 (x, 0) t).hasDerivWithinAt)
    (continuous_const.prodMk (continuous_id.mul continuous_const)).continuousOn
    (fun t ht => by
      rw [hVline x t ⟨ht.1, ht.2.le⟩]
      exact (hd t).hasDerivWithinAt)
    (by simp only [hi, zero_mul])
  simpa only [one_mul] using he (show (1 : Real) ∈ Icc 0 1 by simp)

end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
