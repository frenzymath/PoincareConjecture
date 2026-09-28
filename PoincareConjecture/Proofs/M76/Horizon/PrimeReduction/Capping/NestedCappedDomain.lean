import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.NestedCapFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.RetainedBoundaryCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedCollarCut

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.nested_capped_domain
    {X E ι α : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R P O : Set X} {K C Z : Set E}
    (he : PLDomain e R) (hR : IsCompact R) (hP : IsCompact P)
    (hRP : R ⊆ interior P) (hO : IsOpen O) (hOR : closure O ⊆ interior R)
    (hQ : PLDomain e (P \ O))
    (H : (P \ O : Set X) ≃ₜ K) (f : X → E)
    (hH : ∀ x : (P \ O : Set X), (H x : E) = f x)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hK : IsClosed K) (hC : IsCompact C)
    (hattach : C ∩ K ⊆ f '' (closure O \ O))
    (hZ : IsClosed Z) (hDZ : Disjoint (f '' (R \ O) ∪ C) Z)
    (atlas : α → OpenPartialHomeomorph ((K ∪ C) \ Z : Set E) V3)
    (ha : PLDomain atlas Set.univ)
    (hrep : ∀ i, ∃ (A : Set E) (g : E → V3),
      FinitePiecewiseAffineOn g A ∧
      ∀ x ∈ (atlas i).source, (x : E) ∈ A ∧ atlas i x = g x) :
    PLDomain atlas ((Subtype.val : ((K ∪ C) \ Z : Set E) → E) ⁻¹'
      (f '' (R \ O) ∪ C)) ∧
    IsCompact ((Subtype.val : ((K ∪ C) \ Z : Set E) → E) ⁻¹'
      (f '' (R \ O) ∪ C)) ∧
    frontier ((Subtype.val : ((K ∪ C) \ Z : Set E) → E) ⁻¹'
      (f '' (R \ O) ∪ C)) =
      (Subtype.val : ((K ∪ C) \ Z : Set E) → E) ⁻¹' (f '' frontier R) := by
  let U := interior P \ closure O
  let W := (K ∪ C) \ Z
  have hU : IsOpen U := isOpen_interior.sdiff isClosed_closure
  have hUQ : U ⊆ P \ O :=
    fun _ hx => ⟨interior_subset hx.1, fun hn => hx.2 (subset_closure hn)⟩
  have hRU : frontier R ⊆ U := by
    intro x hx
    exact ⟨hRP (he.closed.frontier_subset hx), fun hn => hx.2 (hOR hn)⟩
  have hRQ : R \ O ⊆ P \ O := fun _ hx => ⟨interior_subset (hRP hx.1), hx.2⟩
  have hFi : InjOn f (P \ O) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))))
  have hdis : Disjoint (f '' U) C := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hyC
    have hyK : f x ∈ K := hH ⟨x, hUQ hx⟩ ▸ (H ⟨x, hUQ hx⟩).property
    obtain ⟨z, hz, hzx⟩ := hattach ⟨hyC, hyK⟩
    have hzQ : z ∈ P \ O := ⟨interior_subset (hRP (interior_subset (hOR hz.1))), hz.2⟩
    exact hx.2 ((hFi hzQ (hUQ hx) hzx) ▸ hz.1)
  have hattachR : C ∩ K ⊆ f '' (interior R \ O) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hattach hy
    exact ⟨x, ⟨hOR hx.1, hx.2⟩, rfl⟩
  obtain ⟨hfront, hcompact⟩ := nested_cap_relative_frontier_off_closed
    hR hRP hO hOR H f hH hK hC.isClosed hattachR hZ hDZ
  have hcompact' := hcompact hC
  obtain ⟨hsmall, _, _, hsmallFront, _, _, _, _, _⟩ :=
    he.nested_collar_cut hR hP hRP hO hOR hQ
  have hW : IsOpen ((Subtype.val : (K ∪ C : Set E) → E) ⁻¹' W) := by
    convert hZ.isOpen_compl.preimage
      (continuous_subtype_val : Continuous (Subtype.val : (K ∪ C : Set E) → E)) using 1
    ext x
    exact and_iff_right x.property
  refine ⟨⟨ha.cover, ha.compatible, hcompact'.isClosed, ?_⟩, hcompact', hfront⟩
  intro p hp
  rw [hfront] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  let xU : U := ⟨x, hRU hx⟩
  have hxsmall : x ∈ frontier (R \ O) := hsmallFront.symm ▸ Or.inl hx
  obtain ⟨hxT, q, ell, v, hell, hxq, hzero, hregion, hlocal, _⟩ :=
    exists_retained_boundary_halfspace_chart hQ hsmall hRQ H f hH hf
      hUQ hU hK hC.isClosed hdis xU hxsmall
  have hxpeq : (⟨f xU, hxT⟩ : (K ∪ C : Set E)) = ⟨p, p.property.1⟩ :=
    Subtype.ext hxp
  rw [hxpeq] at hxq hzero
  obtain ⟨B, hpB, hBzero, hBregion, hBlocal⟩ :=
    exists_open_carrier_halfspace_chart sdiff_subset hW q ell p hxq hzero hregion hlocal
  refine ⟨ell, v, B, hell, hpB, hBzero, ?_, hBregion⟩
  intro i
  obtain ⟨A, g, hg, hgf⟩ := hrep i
  have ht := B.mem_piecewiseAffineGroupoid_transition_of_locallyPL_inverse
    (atlas i) hBlocal hg (fun z hz => (hgf z hz).1) (fun z hz => (hgf z hz).2)
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm ht

end PoincareConjecture.M76
