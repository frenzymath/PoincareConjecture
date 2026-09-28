import PoincareConjecture.Proofs.M02.Topology.AmbientSimplicialGrid

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_finite_polyhedral_neighborhood
    {N : Nat} {S : Set (EuclideanSpace Real (Fin N))}
    (hS : IsCompact S) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N)),
      K.faces.Finite ∧ S ⊆ interior K.space ∧
      ∀ x ∈ K.space, Metric.infDist x S < epsilon := by
  classical
  let E := EuclideanSpace Real (Fin N)
  let h : Real := epsilon / (2 * (N + 1 : Real))
  have hh : 0 < h := by dsimp [h]; positivity
  have hmesh : (N + 1 : Real) * h < epsilon := by
    have hL : 0 < (N + 1 : Real) := by positivity
    have heq : (N + 1 : Real) * h = epsilon / 2 := by
      dsimp [h]
      field_simp
    rw [heq]
    linarith
  obtain ⟨R, hR, hbound⟩ := hS.isBounded.exists_pos_norm_le
  obtain ⟨B, hB⟩ := exists_nat_gt (R / h)
  have hB0 : 0 < B := by
    have hpos : (0 : Real) < B := (div_pos hR hh).trans hB
    exact_mod_cast hpos
  have hRB : R < (B : Real) * h := (div_lt_iff₀ hh).mp hB
  obtain ⟨K0, hfaces, hfinite, hspace⟩ := exists_ambient_grid_complex h hh B hB0
  have hball : Metric.ball (0 : E) ((B : Real) * h) ⊆ K0.space := by
    intro x hx
    rw [hspace]
    intro i
    have hcoord : |x i| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hxnorm : ‖x‖ < (B : Real) * h := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rcases abs_le.mp hcoord with ⟨hlo, hhi⟩
    constructor <;> linarith
  let good : Set (Finset E) := {t | t ∈ K0.faces ∧
    (convexHull Real (t : Set E) ∩ S).Nonempty}
  let selected : Set (Finset E) := {s | s.Nonempty ∧
    ∃ t ∈ good, s ⊆ t}
  have hselected : selected ⊆ K0.faces := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K0.down_closed ht.1 hst hs
  let K : Geometry.SimplicialComplex Real E :=
    { faces := selected
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        obtain ⟨a, ha, hsa⟩ := hs.2
        exact ⟨ht, a, ha, hts.trans hsa⟩
      indep := fun hs => K0.indep (hselected hs)
      inter_subset_convexHull := fun hs ht =>
        K0.inter_subset_convexHull (hselected hs) (hselected ht) }
  have hgood (t : Finset E) (ht : t ∈ good) : t ∈ K.faces :=
    ⟨K0.nonempty_of_mem_faces ht.1, t, ht, Finset.Subset.refl t⟩
  let bad : Set (Finset E) := {t | t ∈ K0.faces ∧
    Disjoint (convexHull Real (t : Set E)) S}
  let A : Set E := ⋃ t ∈ bad, convexHull Real (t : Set E)
  have hbad : bad.Finite := hfinite.subset (fun _ ht => ht.1)
  have hA : IsClosed A := hbad.isClosed_biUnion fun t _ =>
    (t.finite_toSet.isCompact_convexHull Real).isClosed
  let V : Set E := Metric.ball 0 ((B : Real) * h) \ A
  have hV : IsOpen V := Metric.isOpen_ball.inter hA.isOpen_compl
  have hSV : S ⊆ V := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr (by
        simpa only [dist_zero_right] using (hbound x hx).trans_lt hRB)
    · intro hxA
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxA
      exact Set.disjoint_left.mp ht.2 hxt hx
  have hVK : V ⊆ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp (hball hx.1)
    have htgood : t ∈ good := by
      refine ⟨ht, ?_⟩
      by_contra hn
      have htb : t ∈ bad := ⟨ht, Set.disjoint_left.mpr fun y hy hyS => hn ⟨y, hy, hyS⟩⟩
      exact hx.2 (Set.mem_iUnion₂.mpr ⟨t, htb, hxt⟩)
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, hgood t htgood, hxt⟩
  refine ⟨K, hfinite.subset hselected,
    hSV.trans (interior_maximal hVK hV), ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hs.2
  obtain ⟨y, hyt, hyS⟩ := ht.2
  have hxt : x ∈ convexHull Real (t : Set E) := convexHull_mono hst hxs
  have hdiam : Metric.diam (convexHull Real (t : Set E)) ≤ (N + 1 : Real) * h := by
    have htface := ht.1
    rw [hfaces] at htface
    obtain ⟨htnonempty, z, pi, _hz, htgrid⟩ := htface
    exact (ambient_grid_simplex_geometry h hh z pi t htnonempty htgrid).2.2.1
  exact ((Metric.infDist_le_dist_of_mem hyS).trans
    ((Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull Real).isBounded
      hxt hyt).trans hdiam)).trans_lt hmesh

end PoincareConjecture.Proofs.M02.Topology
