


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Sides







set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface


noncomputable def graphVerticalReflection : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ (M := ℝ))

@[simp] theorem graphVerticalReflection_apply (q : ℝ × ℝ) :
    graphVerticalReflection q = (q.1, -q.2) := rfl

@[simp] theorem graphVerticalReflection_symm_apply (q : ℝ × ℝ) :
    graphVerticalReflection.symm q = (q.1, -q.2) := rfl

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



theorem exists_graph_frame_into_incident_region (e : D.EdgeIndex) (q : D.regions)
    (hq : q = D.regionLeft e ∨ q = D.regionRight e)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ)
    {a b l r : ℝ} (hab : a ≤ b) (hla : l < a) (hbr : b < r)
    (ha : 0 < a) (hb : b < 1) (hGsource : G.source = Ioo l r)
    (hmono : StrictMonoOn G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hgraph_source : ∀ x ∈ G.target, L.symm (x, h x) ∈ C.source)
    (hgraph : ∀ t ∈ G.source, (D.edge e.1 e.2).map t = C (L.symm (G t, h (G t)))) :
    ∃ (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) (f : ℝ → ℝ) (α β δ : ℝ),
      (∀ z, (A z).1 = (L z).1) ∧ ContDiffOn ℝ ∞ f G.target ∧
      (∀ x ∈ G.target, A.symm (x, f x) ∈ C.source) ∧
      (∀ t ∈ G.source, (D.edge e.1 e.2).map t = C (A.symm (G t, f (G t)))) ∧
      α < G a ∧ G b < β ∧ 0 < δ ∧
      ∀ x ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
        A.symm (x, f x + z) ∈ C.source ∧
        (C (A.symm (x, f x + z)) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
        (C (A.symm (x, f x + z)) ∈ connectedComponentIn
          (chartDiskBoundaryUnion D.centers D.radius)ᶜ q ↔ 0 < z) ∧
        (0 ≤ z → C (A.symm (x, f x + z)) ∈ closure (connectedComponentIn
          (chartDiskBoundaryUnion D.centers D.radius)ᶜ q)) := by
  let F := linearGraphCoordinates C L
  have hsource (x : ℝ) (hx : x ∈ G.target) :
      collarParameterEquiv.symm (x, h x) ∈ F.source := by
    refine ⟨mem_univ _, ?_⟩
    change L.symm (collarParameterEquiv (collarParameterEquiv.symm (x, h x))) ∈ C.source
    simpa only [collarParameterEquiv.apply_symm_apply] using hgraph_source x hx
  have hmap (t : ℝ) (ht : t ∈ G.source) : (D.edge e.1 e.2).map t =
      F (collarParameterEquiv.symm (G t, h (G t))) := by
    simpa only [F, linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply] using hgraph t ht
  obtain ⟨α, β, δ, upper, lower, hα, hβ, hδ, hne, hpair, htube⟩ :=
    D.exists_edge_graph_incident_regions e F G h hab hla hbr ha hb hGsource hmono hh hsource hmap
  have htube' (x : ℝ) (hx : x ∈ Ioo α β) (z : ℝ) (hz : |z| < δ) := htube x hx z hz
  simp only [F, linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply] at htube'
  have hdis : Disjoint
      (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper)
      (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower) := by
    apply disjoint_left.mpr
    intro p hp hp'
    exact hne (Subtype.ext (D.regions_distinct upper upper.property lower lower.property
      ((connectedComponentIn_eq hp).trans (connectedComponentIn_eq hp').symm)))
  have hupper (x : ℝ) (hx : x ∈ Ioo α β) (z : ℝ) (hz : |z| < δ) :
      C (L.symm (x, h x + z)) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ upper ↔ 0 < z := by
    have hloc := htube' x hx z hz
    refine ⟨?_, hloc.2.2.1⟩
    intro hp
    rcases lt_trichotomy z 0 with hneg | hzero | hpos
    · exact False.elim (disjoint_left.mp hdis hp (hloc.2.2.2.1 hneg))
    · exact False.elim (connectedComponentIn_subset _ _ hp (hloc.2.1.mpr hzero))
    · exact hpos
  have hlower (x : ℝ) (hx : x ∈ Ioo α β) (z : ℝ) (hz : |z| < δ) :
      C (L.symm (x, h x + z)) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ lower ↔ z < 0 := by
    have hloc := htube' x hx z hz
    refine ⟨?_, hloc.2.2.2.1⟩
    intro hp
    rcases lt_trichotomy z 0 with hneg | hzero | hpos
    · exact hneg
    · exact False.elim (connectedComponentIn_subset _ _ hp (hloc.2.1.mpr hzero))
    · exact False.elim (disjoint_left.mp hdis (hloc.2.2.1 hpos) hp)
  rcases (hpair q).mpr hq with hqu | hql
  · subst q
    refine ⟨L, h, α, β, δ, fun _ => rfl, hh, hgraph_source, hgraph, hα, hβ, hδ, ?_⟩
    intro x hx z hz
    have hloc := htube' x hx z hz
    exact ⟨hloc.1.2, hloc.2.1, hupper x hx z hz, hloc.2.2.2.2.1⟩
  · subst q
    let A := L.trans graphVerticalReflection
    have hA (x y : ℝ) : A.symm (x, y) = L.symm (x, -y) := rfl
    have hAz (x z : ℝ) : A.symm (x, -h x + z) = L.symm (x, h x + -z) := by
      rw [hA]
      congr 2
      ring
    refine ⟨A, fun x => -h x, α, β, δ, fun _ => rfl, hh.neg, ?_, ?_, hα, hβ, hδ, ?_⟩
    · intro x hx
      simpa only [hA, neg_neg] using hgraph_source x hx
    · intro t ht
      simpa only [hA, neg_neg] using hgraph t ht
    · intro x hx z hz
      have hz' : |-z| < δ := by simpa only [abs_neg] using hz
      have hloc := htube' x hx (-z) hz'
      rw [hAz]
      refine ⟨hloc.1.2, ?_, ?_, fun h => hloc.2.2.2.2.2 (neg_nonpos.mpr h)⟩
      · simpa only [neg_eq_zero] using hloc.2.1
      · simpa only [neg_neg_iff_pos] using hlower x hx (-z) hz'

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
