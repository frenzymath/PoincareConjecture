import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Graph



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]




theorem exists_supported_transport_between_graphs
    (α b : E → Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b)
    (hα : ContinuousOn α (tsupport b))
    {O : Set (E × Real)} (hO : IsOpen O)
    (htrace : ∀ x ∈ tsupport b, ∀ t ∈ Icc (0 : Real) 1,
      (x, α x + t * b x) ∈ O) :
    ∃ K : Set (E × Real), IsCompact K ∧ K ⊆ O ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∉ K, F p = p) ∧
        ∀ x, F (x, α x) = (x, α x + b x) := by
  let T : Set (E × Real) :=
    (fun p : E × Real => (p.1, α p.1 + p.2 * b p.1)) '' (tsupport b ×ˢ Icc 0 1)
  have hT : IsCompact T := (hbc.prod isCompact_Icc).image_of_continuousOn
    (continuousOn_fst.prodMk ((hα.comp continuousOn_fst (fun _ hp => hp.1)).add
      (continuousOn_snd.mul (hb.continuous.comp continuous_fst).continuousOn)))
  have hTO : T ⊆ O := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact htrace x hx t ht
  obtain ⟨K, hK, hTK, hKO⟩ := exists_compact_between hT hO hTO
  obtain ⟨χ, hχ, hχzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, E × Real)
      hT.isClosed hTK (n := ⊤)
  let V : E × Real → E × Real := fun p => (0, χ p * b p.1)
  have hV : ContDiff Real ∞ V :=
    contDiff_const.prodMk (χ.contMDiff.contDiff.mul (hb.comp contDiff_fst))
  have hVzero (p : E × Real) (hp : p ∉ K) : V p = 0 := by
    simp [V, hχzero p hp]
  have hVline (x : E) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      V (x, α x + t * b x) = (0, b x) := by
    by_cases hx : x ∈ tsupport b
    · have hmem : (x, α x + t * b x) ∈ T := ⟨(x, t), ⟨hx, ht⟩, rfl⟩
      simp only [V, hχ.self_of_nhdsSet _ hmem, one_mul]
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
  refine ⟨K, hK, hKO, Φ 0 1, hfirst 0 1, hfix 0 1, ?_⟩
  intro x
  have hd (t : Real) : HasDerivAt (fun r : Real => (x, α x + r * b x)) (0, b x) t := by
    simpa using (hasDerivAt_const t x).prodMk
      (((hasDerivAt_id t).mul_const (b x)).const_add (α x))
  have he := ODE_solution_unique (v := fun _ => V) (fun _ => hL)
    (f := fun t => Φ 0 t (x, α x)) (g := fun t : Real => (x, α x + t * b x))
    ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (fun t _ => (ho 0 (x, α x) t).hasDerivWithinAt)
    (continuous_const.prodMk (continuous_const.add
      (continuous_id.mul continuous_const))).continuousOn
    (fun t ht => by
      rw [hVline x t ⟨ht.1, ht.2.le⟩]
      exact (hd t).hasDerivWithinAt)
    (by simp only [hi, zero_mul, add_zero])
  simpa only [one_mul] using he (show (1 : Real) ∈ Icc 0 1 by simp)



theorem exists_positive_graph_transport
    (α b : E → Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b)
    (hα : ContinuousOn α (tsupport b))
    (hαpos : ∀ x ∈ tsupport b, 0 < α x)
    (hβpos : ∀ x ∈ tsupport b, 0 < α x + b x) :
    ∃ K : Set (E × Real), IsCompact K ∧ K ⊆ {p | 0 < p.2} ∧
      ∃ F : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞,
        (∀ p, (F p).1 = p.1) ∧
        (∀ p ∉ K, F p = p) ∧
        (∀ p, p.2 ≤ 0 → F p = p) ∧
        ∀ x, F (x, α x) = (x, α x + b x) := by
  obtain ⟨K, hK, hKO, F, hFfirst, hFfix, hFgraph⟩ :=
    exists_supported_transport_between_graphs α b hb hbc hα
      (isOpen_lt continuous_const continuous_snd) (fun x hx t ht => by
        change 0 < α x + t * b x
        have h0 := hαpos x hx
        have h1 := hβpos x hx
        by_cases hb0 : 0 ≤ b x
        · exact add_pos_of_pos_of_nonneg h0 (mul_nonneg ht.1 hb0)
        · have hmul := mul_le_mul_of_nonpos_right ht.2 (le_of_not_ge hb0)
          nlinarith)
  exact ⟨K, hK, hKO, F, hFfirst, hFfix,
    fun p hp => hFfix p (fun h => (not_lt_of_ge hp) (hKO h)), hFgraph⟩

end Poincare.Manifold.Schoenflies
