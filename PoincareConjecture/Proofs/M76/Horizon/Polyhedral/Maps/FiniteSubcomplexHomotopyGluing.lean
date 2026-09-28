import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

variable {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [Finite κ]

theorem exists_homotopy_of_finite_subcomplex_cover
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJK : ∀ i, J i ≤ K)
    (hcover : K.space ⊆ ⋃ i, (J i).space)
    (H : ∀ i, C(I × (J i).space, X))
    (hagree : ∀ i j (t : I) (x : E) (hi : x ∈ (J i).space) (hj : x ∈ (J j).space),
      H i (t, ⟨x, hi⟩) = H j (t, ⟨x, hj⟩)) :
    ∃ G : C(I × K.space, X), ∀ i (t : I) (x : (J i).space),
      G (t, ⟨x, space_subset_of_le (hJK i) x.property⟩) = H i (t, x) := by
  classical
  let S : κ → Set (I × K.space) := fun i => {z | (z.2 : E) ∈ (J i).space}
  let p (i : κ) : C(S i, I × (J i).space) :=
    ⟨fun z => (z.val.1, ⟨z.val.2, z.property⟩),
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)⟩
  let F (i : κ) : C(S i, X) := (H i).comp (p i)
  have hF : ∀ i j (z : I × K.space) (hi : z ∈ S i) (hj : z ∈ S j),
      F i ⟨z, hi⟩ = F j ⟨z, hj⟩ := by
    intro i j z hi hj
    exact hagree i j z.1 z.2 hi hj
  have hS : ⋃ i, S i = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover z.2.property)
    exact ⟨i, hi⟩
  let g := Set.liftCover S (fun i => F i) hF hS
  have hval (i : κ) (z : S i) : g z = F i z := Set.liftCover_coe z
  have hg : Continuous g := by
    apply (locallyFinite_of_finite S).continuous hS
    · intro i
      exact ((J i).isCompact_space_of_finite (hK.subset (hJK i))).isClosed.preimage
        (continuous_subtype_val.comp continuous_snd)
    · intro i
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : (S i).domRestrict g = F i := funext (hval i)
      rw [heq]
      exact (F i).continuous
  refine ⟨⟨g, hg⟩, ?_⟩
  intro i t x
  exact hval i ⟨(t, ⟨x, space_subset_of_le (hJK i) x.property⟩), x.property⟩

theorem exists_polyhedralPL_homotopy_of_finite_subcomplex_cover
    [FiniteDimensional ℝ E] {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V)
    (hcover_e : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJK : ∀ i, J i ≤ K)
    (hcover : K.space ⊆ ⋃ i, (J i).space)
    (H : ∀ i, C(I × (J i).space, X))
    (hagree : ∀ i j (t : I) (x : E) (hi : x ∈ (J i).space) (hj : x ∈ (J j).space),
      H i (t, ⟨x, hi⟩) = H j (t, ⟨x, hj⟩))
    (f : κ → E → X) (hf : ∀ i, PolyhedralPLInCharts e (f i) (J i).space)
    (hfinal : ∀ i (x : (J i).space), H i (1, x) = f i x) :
    ∃ (G : C(I × K.space, X)) (q : E → X),
      (∀ i (t : I) (x : (J i).space),
        G (t, ⟨x, space_subset_of_le (hJK i) x.property⟩) = H i (t, x)) ∧
      (∀ x : K.space, G (1, x) = q x) ∧
      (∀ i, EqOn q (f i) (J i).space) ∧ PolyhedralPLInCharts e q K.space := by
  classical
  obtain ⟨G, hG⟩ := K.exists_homotopy_of_finite_subcomplex_cover hK J hJK hcover H hagree
  let q : E → X := fun x => if hx : x ∈ K.space then G (1, ⟨x, hx⟩) else Classical.ofNonempty
  have hq (x : K.space) : q x = G (1, x) := by simp only [q, dif_pos x.property]
  have hqi (i : κ) : EqOn q (f i) (J i).space := by
    intro x hx
    exact (hq ⟨x, space_subset_of_le (hJK i) hx⟩).trans
      ((hG i 1 ⟨x, hx⟩).trans (hfinal i ⟨x, hx⟩))
  have hqc : ContinuousOn q K.space := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : K.space.domRestrict q = fun x : K.space => G (1, x) := funext hq
    rw [heq]
    exact G.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨G, q, hG, fun x => (hq x).symm, hqi, ?_⟩
  exact polyhedralPLInCharts_of_finite_cover hcover_e hcompat K hK J
    (fun i => hK.subset (hJK i)) hqc (fun i => (hf i).congr (hqi i).symm) hcover

end Geometry.SimplicialComplex
