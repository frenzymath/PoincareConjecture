import PoincareConjecture.Proofs.M40.Mathlib.CompactChartMargin
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Data.Fintype.EquivFin










set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M60

variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace F]
  [MetricSpace N] [ChartedSpace F N]




theorem exists_finite_relative_charts (f₀ : C(E, N)) {K O : Set E}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ (n : ℕ) (c : Fin n → N) (rho : Fin n → E → ℝ) (margin : ℝ),
      0 < margin ∧
      (∀ i, ContDiff ℝ ∞ (rho i)) ∧
      (∀ i x, rho i x ∈ Icc 0 1) ∧
      (∀ i, IsCompact (tsupport (rho i))) ∧
      (∀ i, tsupport (rho i) ⊆ O) ∧
      (∀ x ∈ K, ∃ i, rho i =ᶠ[𝓝 x] 1) ∧
      (∀ f : E → N, (∀ x, dist (f x) (f₀ x) < margin) →
        ∀ i, MapsTo f (tsupport (rho i)) (chartAt F (c i)).source) := by
  classical
  have hbump (x : K) : ∃ rho : SmoothBumpFunction 𝓘(ℝ, E) (x : E),
      tsupport rho ⊆ O ∩ f₀ ⁻¹' (chartAt F (f₀ x)).source := by
    have hn : O ∩ f₀ ⁻¹' (chartAt F (f₀ x)).source ∈ 𝓝 (x : E) :=
      inter_mem (hO.mem_nhds (hKO x.property))
        (f₀.continuous.continuousAt.preimage_mem_nhds
          ((chartAt F (f₀ x)).open_source.mem_nhds (mem_chart_source F (f₀ x))))
    obtain ⟨rho, -, hrho⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : E)).mem_iff.mp hn
    exact ⟨rho, hrho⟩
  choose rho hrho using hbump
  let W : K → Set E := fun x => interior {y | rho x y = 1}
  have hcover : K ⊆ ⋃ x : K, W x := by
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (rho ⟨x, hx⟩).eventuallyEq_one⟩
  obtain ⟨A, hA⟩ := hK.elim_finite_subcover W (fun _ => isOpen_interior) hcover
  let j : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let c := fun i : Fin (Fintype.card A) => f₀ (j i).val.val
  let r := fun i : Fin (Fintype.card A) => (rho (j i).val : E → ℝ)
  have hcompact (i : Fin (Fintype.card A)) : IsCompact (tsupport (r i)) :=
    (rho (j i).val).hasCompactSupport
  obtain ⟨margin, hmargin, hvalid⟩ := Proofs.M40.exists_pos_uniform_mapsTo_of_edist_lt
    (fun i => tsupport (r i)) (fun i => (chartAt F (c i)).source) f₀ hcompact
    (fun i => (chartAt F (c i)).open_source) (fun _ => f₀.continuous.continuousOn)
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
  · intro f hf
    apply hvalid f
    intro x
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hmargin).mpr (hf x)

end PoincareConjecture.M60
