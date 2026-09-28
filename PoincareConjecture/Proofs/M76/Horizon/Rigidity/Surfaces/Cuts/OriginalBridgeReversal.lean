import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutArcPairing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

private theorem interval_endpoints_ne
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {s : Set X} {a b : X} (hs : IsFinitePLBallPair ℝ s {a, b}) : a ≠ b := by
  intro he
  have h := hs.ncard_boundary_eq_two
  simp only [he, pair_eq_singleton, Set.ncard_singleton] at h
  norm_num at h

theorem endpoint_pair_reversal_of_scalar
    {X : Type*} {Y : Type*} [LinearOrder Y]
    {f : X → Y} {a b c d : X}
    (hab : a ≠ b) (hset : ({c, d} : Set X) = {a, b})
    (hforward : f a < f b) (hreverse : f d < f c) :
    c = b ∧ d = a := by
  rcases Set.pair_eq_pair_iff.mp hset with ⟨hca, hdb⟩ | ⟨hcb, hda⟩
  · rw [hca, hdb] at hreverse
    exact (False.elim ((not_lt_of_ge hforward.le) hreverse))
  · exact ⟨hcb, hda⟩

theorem ordered_middle_parameters
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {g : ℝ → X} (hg : FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1))
    (hi : InjOn g (Icc (0 : ℝ) 1)) {left middle right : Set X} {a b : X}
    (hl : IsFinitePLBallPair ℝ left {g 0, a})
    (hm : IsFinitePLBallPair ℝ middle {a, b})
    (hr : IsFinitePLBallPair ℝ right {b, g 1})
    (hls : left ⊆ g '' Icc (0 : ℝ) 1)
    (hms : middle ⊆ g '' Icc (0 : ℝ) 1)
    (hrs : right ⊆ g '' Icc (0 : ℝ) 1) (hdis : Disjoint left right) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ β < 1 ∧ g α = a ∧ g β = b ∧
      middle = g '' Icc α β := by
  obtain ⟨α, hα, hga⟩ := hls (hl.1 (Or.inr rfl))
  obtain ⟨β, hβ, hgb⟩ := hrs (hr.1 (Or.inl rfl))
  have h0α : 0 < α := by
    by_contra h
    have ha0 : α = 0 := le_antisymm (le_of_not_gt h) hα.1
    exact interval_endpoints_ne hl (ha0 ▸ hga)
  have hβ1 : β < 1 := by
    by_contra h
    have hb1 : β = 1 := le_antisymm hβ.2 (le_of_not_gt h)
    exact interval_endpoints_ne hr (hgb.symm.trans (congrArg g hb1))
  have hleft : left = g '' Icc 0 α := by
    apply (show IsFinitePLBallPair ℝ left {g 0, g α} by rwa [hga]).eq_image_Icc_of_subset
      hg hi h0α (fun _ hx ↦ ⟨hx.1, hx.2.trans hα.2⟩) hls
  have hαβ : α < β := by
    by_contra h
    have hmem : g β ∈ left := hleft.symm ▸
      (show g β ∈ g '' Icc 0 α from ⟨β, ⟨hβ.1, le_of_not_gt h⟩, rfl⟩)
    exact disjoint_left.mp hdis hmem (hgb.symm ▸ hr.1 (Or.inl rfl))
  refine ⟨α, β, h0α, hαβ, hβ1, hga, hgb, ?_⟩
  exact (show IsFinitePLBallPair ℝ middle {g α, g β} by rwa [hga, hgb]).eq_image_Icc_of_subset
    hg hi hαβ (fun _ hx ↦ ⟨hα.1.trans hx.1, hx.2.trans hβ.2⟩) hms

namespace OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

theorem exists_ordered_longArc_bridge_chart (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i : Fin 4) :
    ∃ (g : ℝ → ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))) (α β : ℝ),
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1) ∧ InjOn g (Icc (0 : ℝ) 1) ∧
      g '' Icc (0 : ℝ) 1 = A.longBoundaryArc i ∧
      g 0 = A.gapCenter (i - 1) ∧ g 1 = A.gapCenter i ∧
      0 < α ∧ α < β ∧ β < 1 ∧ g α = A.bridgeBegin i ∧ g β = A.bridgeEnd i ∧
      g '' Icc α β = A.boundaryBridge i ∧
      InjOn (A.sourceMap ∘ g) (Icc α β) ∧
      (A.sourceMap ∘ g) '' Icc α β = A.sourceBridge i := by
  have hd := A.longBoundaryArc_isFinitePLInterval hbound i
  have hend : A.gapCenter (i - 1) ≠ A.gapCenter i :=
    A.gapCenters_injective.ne (by fin_cases i <;> decide)
  obtain ⟨e, he, he0, he1⟩ := hd.exists_unitInterval_chart_with_endpoints hend
  obtain ⟨g, hg, hge⟩ := he
  have hgi : InjOn g (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hge ⟨x, hx⟩).trans (hxy.trans (hge ⟨y, hy⟩).symm))))
  have hgs : g '' Icc (0 : ℝ) 1 = A.longBoundaryArc i := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hge ⟨x, hx⟩ ▸ (e ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hge x).symm.trans (congrArg Subtype.val hx)⟩
  have hg0 : g 0 = A.gapCenter (i - 1) := (hge ⟨0, by norm_num⟩).symm.trans he0
  have hg1 : g 1 = A.gapCenter i := (hge ⟨1, by norm_num⟩).symm.trans he1
  have hleft : IsFinitePLBallPair ℝ (A.gapSpokes (i - 1)).right {g 0, A.bridgeBegin i} := by
    simpa only [hg0, sub_add_cancel] using (A.gapSpokes (i - 1)).right_ball
  have hright : IsFinitePLBallPair ℝ (A.gapSpokes i).left {A.bridgeEnd i, g 1} := by
    simpa only [hg1, pair_comm] using (A.gapSpokes i).left_ball
  have hdis : Disjoint (A.gapSpokes (i - 1)).right (A.gapSpokes i).left :=
    (A.gapSpokes_different_disjoint (by fin_cases i <;> decide)).mono
      subset_union_right subset_union_left
  obtain ⟨α, β, hα, hαβ, hβ, hga, hgb, hmiddle⟩ := ordered_middle_parameters hg hgi
    hleft (A.boundaryBridge_interval i) hright
    (hgs.symm ▸ (subset_union_left.trans subset_union_left))
    (hgs.symm ▸ (subset_union_right.trans subset_union_left))
    (hgs.symm ▸ subset_union_right) hdis
  have hsub : Icc α β ⊆ Icc (0 : ℝ) 1 :=
    fun x hx ↦ ⟨hα.le.trans hx.1, hx.2.trans hβ.le⟩
  refine ⟨g, α, β, hg, hgi, hgs, hg0, hg1, hα, hαβ, hβ, hga, hgb, hmiddle.symm, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hgi (hsub hx) (hsub hy) (A.sourceMap_injOn_boundaryBridge i
      (hmiddle.symm ▸ mem_image_of_mem g hx) (hmiddle.symm ▸ mem_image_of_mem g hy) hxy)
  · rw [image_comp, ← hmiddle]
    exact A.sourceMap_boundaryBridge i

theorem source_bridge_endpoint_reversal_of_scalar
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4)
    (ell : E →ₗ[ℝ] ℝ)
    (hforward : ell (A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i)) <
      ell (A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i)))
    (hreverse : ell (A.sourceMap K P D hD hcofaces hP labels
        (A.bridgeEnd (A.arcPairing i))) <
      ell (A.sourceMap K P D hD hcofaces hP labels
        (A.bridgeBegin (A.arcPairing i)))) :
    A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin (A.arcPairing i)) =
        A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd i) ∧
      A.sourceMap K P D hD hcofaces hP labels (A.bridgeEnd (A.arcPairing i)) =
        A.sourceMap K P D hD hcofaces hP labels (A.bridgeBegin i) := by
  have hset := A.source_bridge_endpoints_paired i
  obtain ⟨h0, h1⟩ := endpoint_pair_reversal_of_scalar
    (fun h ↦ by
      rw [h] at hforward
      exact (lt_irrefl _ hforward)) hset hforward hreverse
  exact ⟨h0, h1⟩

end OriginalPrimalCutDiskData

end PoincareConjecture.M76.OriginalTriangleCopies
