import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AffineOnFaces.graph_vertex_bounds
    {K : SimplicialComplex ℝ E} {g : E → ℝ × E} (hg : K.AffineOnFaces g)
    (hvertices : ∀ v ∈ K.vertices, g v = 0 ∨ g v = (1, v))
    {x : E} (hx : x ∈ K.space) :
    0 ≤ (g x).1 ∧ (g x).1 ≤ 1 ∧ ((g x).1 = 1 → (g x).2 = x) := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hg s hs
  obtain ⟨w, hw, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxs
  have hv (v : E) (hvs : v ∈ s) : g v = 0 ∨ g v = (1, v) := by
    apply hvertices v
    rw [vertices_eq]
    exact mem_biUnion hs hvs
  have hformula : g x = ∑ v ∈ s, w v • g v := by
    calc
      g x = a x := ha hxs
      _ = ∑ v ∈ s, w v • a v := by
        change a.toAffineMap x = ∑ v ∈ s, w v • a.toAffineMap v
        have hmap := s.map_affineCombination id w hw1 a.toAffineMap
        simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw1,
          Function.comp_apply, id_eq, hwx] using hmap
      _ = ∑ v ∈ s, w v • g v := by
        apply Finset.sum_congr rfl
        intro v hvs
        rw [ha (subset_convexHull ℝ _ hvs)]
  have hfst : (g x).1 = ∑ v ∈ s, w v * (g v).1 := by
    simpa only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using
      congrArg Prod.fst hformula
  have hunit (v : E) (hvs : v ∈ s) : 0 ≤ (g v).1 ∧ (g v).1 ≤ 1 := by
    rcases hv v hvs with hzero | hgraph
    · simp [hzero]
    · simp [hgraph]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfst]
    exact Finset.sum_nonneg (fun v hvs => mul_nonneg (hw v hvs) (hunit v hvs).1)
  · rw [hfst, ← hw1]
    apply Finset.sum_le_sum
    intro v hvs
    exact (mul_le_mul_of_nonneg_left (hunit v hvs).2 (hw v hvs)).trans_eq (mul_one _)
  · intro hone
    have hsum : ∑ v ∈ s, w v * (1 - (g v).1) = 0 := by
      simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [hw1, ← hfst, hone, sub_self]
    have hweight (v : E) (hvs : v ∈ s) (hzero : g v = 0) : w v = 0 := by
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v hvs => mul_nonneg (hw v hvs) (sub_nonneg.mpr (hunit v hvs).2))).mp
          hsum v hvs
      simpa [hzero] using hterm
    have hsnd : (g x).2 = ∑ v ∈ s, w v • (g v).2 := by
      simpa only [Prod.snd_sum, Prod.smul_snd] using congrArg Prod.snd hformula
    rw [hsnd, ← hwx]
    apply Finset.sum_congr rfl
    intro v hvs
    rcases hv v hvs with hzero | hgraph
    · simp [hweight v hvs hzero]
    · simp [hgraph]

variable [FiniteDimensional ℝ E]

theorem exists_supported_graph_extension (J K : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hK : K.faces.Finite) (hJK : J.space ⊆ K.space)
    {U : Set E} (hU : IsOpen U) (hJU : J.space ⊆ U) :
    ∃ g : E → ℝ × E, FinitePiecewiseAffineOn g K.space ∧
      EqOn g (fun x => (1, x)) J.space ∧
      (∀ x, x ∉ U → g x = 0) ∧ (∀ x, x ∉ K.space → g x = 0) ∧
      (∀ x, 0 ≤ (g x).1 ∧ (g x).1 ≤ 1) ∧
      (∀ x, (g x).1 = 1 → (g x).2 = x) := by
  classical
  let a : E →ᴬ[ℝ] ℝ × E :=
    (ContinuousAffineMap.const ℝ E (1 : ℝ)).prod (ContinuousAffineMap.id ℝ E)
  have ha : FinitePiecewiseAffineOn (fun x : E => ((1 : ℝ), x)) J.space :=
    ⟨J, hJ, rfl, J.affineOnFaces_affine a⟩
  obtain ⟨g, R, hR, hRK, hg, hgv, heq, hzeroU, hzeroK⟩ :=
    ha.exists_supported_extension_of_eq_zero_off_with_vertices K hK hJK ha.isCompact
      (fun _ hx hn => False.elim (hn hx)) hU hJU
  have hvertices (v : E) (hv : v ∈ R.vertices) : g v = 0 ∨ g v = (1, v) := by
    rw [hgv hv]
    by_cases hvJ : v ∈ J.space
    · exact Or.inr (indicator_of_mem hvJ _)
    · exact Or.inl (indicator_of_notMem hvJ _)
  refine ⟨g, ⟨R, hR, hRK, hg⟩, heq, hzeroU, hzeroK, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ K.space
    · have hbounds := hg.graph_vertex_bounds hvertices (hRK.symm ▸ hx)
      exact ⟨hbounds.1, hbounds.2.1⟩
    · simp [hzeroK x hx]
  · intro x hxone
    by_cases hx : x ∈ K.space
    · exact (hg.graph_vertex_bounds hvertices (hRK.symm ▸ hx)).2.2 hxone
    · simp [hzeroK x hx] at hxone

end Geometry.SimplicialComplex
