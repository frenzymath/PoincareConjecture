import PoincareConjecture.Proofs.M60.Mathlib.FiniteRelativeCharts













set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64Uniformization

variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace F] [MetricSpace N] [ChartedSpace F N]





theorem scalar_exists_finite_relative_charts (f : E → N) {K O : Set E}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hf : ContinuousOn f O) :
    ∃ (n : ℕ) (c : Fin n → N) (rho : Fin n → E → ℝ) (margin : ℝ),
      0 < margin ∧
      (∀ i, ContDiff ℝ ∞ (rho i)) ∧
      (∀ i x, rho i x ∈ Icc 0 1) ∧
      (∀ i, IsCompact (tsupport (rho i))) ∧
      (∀ i, tsupport (rho i) ⊆ O) ∧
      (∀ x ∈ K, ∃ i, rho i =ᶠ[𝓝 x] 1) ∧
      (∀ f' : E → N, (∀ x, dist (f' x) (f x) < margin) →
        ∀ i, MapsTo f' (tsupport (rho i)) (chartAt F (c i)).source) := by
  classical
  have hbump (x : K) : ∃ rho : SmoothBumpFunction 𝓘(ℝ, E) (x : E),
      tsupport rho ⊆ O ∩ f ⁻¹' (chartAt F (f x)).source := by
    have hn : O ∩ f ⁻¹' (chartAt F (f x)).source ∈ 𝓝 (x : E) :=
      inter_mem (hO.mem_nhds (hKO x.property))
        ((hf.continuousAt (hO.mem_nhds (hKO x.property))).preimage_mem_nhds
          ((chartAt F (f x)).open_source.mem_nhds (mem_chart_source F (f x))))
    obtain ⟨rho, -, hrho⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : E)).mem_iff.mp hn
    exact ⟨rho, hrho⟩
  choose rho hrho using hbump
  let W : K → Set E := fun x => interior {y | rho x y = 1}
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩,
      mem_interior_iff_mem_nhds.mpr (rho ⟨x, hx⟩).eventuallyEq_one⟩
  obtain ⟨A, hA⟩ := hK.elim_finite_subcover W (fun _ => isOpen_interior) hcover
  let j : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let c := fun i : Fin (Fintype.card A) => f (j i).val.val
  let r := fun i : Fin (Fintype.card A) => (rho (j i).val : E → ℝ)
  have hcompact (i : Fin (Fintype.card A)) : IsCompact (tsupport (r i)) :=
    (rho (j i).val).hasCompactSupport
  obtain ⟨margin, hmargin, hvalid⟩ := Proofs.M40.exists_pos_uniform_mapsTo_of_edist_lt
    (fun i => tsupport (r i)) (fun i => (chartAt F (c i)).source) f hcompact
    (fun i => (chartAt F (c i)).open_source)
    (fun i => hf.mono (fun _ hx => (hrho (j i).val hx).1))
    (fun i _ hx => (hrho (j i).val hx).2)
  refine ⟨Fintype.card A, c, r, margin, hmargin,
    (fun i => (rho (j i).val).contMDiff.contDiff),
    (fun i _ => (rho (j i).val).mem_Icc), hcompact,
    (fun i _ hx => (hrho (j i).val hx).1), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyA, hy⟩ := mem_iUnion₂.mp (hA hx)
    obtain ⟨i, hi⟩ := j.surjective ⟨y, hyA⟩
    refine ⟨i, ?_⟩
    have hi' : (j i).val = y := congrArg Subtype.val hi
    change (rho (j i).val : E → ℝ) =ᶠ[𝓝 x] 1
    rw [hi']
    exact mem_interior_iff_mem_nhds.mp hy
  · intro f' hf'
    apply hvalid f'
    intro x
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hmargin).mpr (hf' x)

end PoincareConjecture.M64Uniformization
