import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLMarkedCycle
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimFinitePL











set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]





theorem exists_marked_square_image_cycle {a : V2 → E}
    (ha : FinitePiecewiseAffineOn a Q) (gamma : C(Q, X))
    (j : C(a '' Q, X))
    (hj : ∀ x : Q, j ⟨a x, mem_image_of_mem a x.property⟩ = gamma x)
    {b : X} (p : Path b (gamma squareRimBase))
    (J : Subgroup (FundamentalGroup X b))
    (houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J) :
    ∃ (K : SimplicialComplex ℝ E) (himage : K.space ⊆ a '' Q) (G : C(K.space, X)),
      K.space = (a ∘ squareRimParameter) '' Icc (0 : ℝ) 1 ∧
      (∀ x : K.space, G x = j ⟨x, himage x.property⟩) ∧
      K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 2) ∧
      ∃ (v : K.vertices) (c : K.vertexAbstractComplex.edgeGraph.Walk v v)
        (q : Path b (G ⟨v, K.vertices_subset_space v.property⟩)),
        c.IsCycle ∧ q.whiskeredLoopClass
          ((K.geometricWalkPath c).map G.continuous) ∉ J := by
  classical
  let f := a ∘ squareRimParameter
  obtain ⟨hf, hformula⟩ := finitePL_squareRim_composition ha
  have hclosed : f 1 = f 0 := by
    have hzero := hformula (0 : unitInterval)
    have hone := hformula (1 : unitInterval)
    simp only [Set.Icc.coe_zero, Path.source] at hzero
    simp only [Set.Icc.coe_one, Path.target] at hone
    exact hone.trans hzero.symm
  have himageQ : f '' Icc (0 : ℝ) 1 ⊆ a '' Q := by
    rintro _ ⟨t, _, rfl⟩
    exact mem_image_of_mem a (squareRimLoop.extend t).property
  let inc : C(f '' Icc (0 : ℝ) 1, a '' Q) :=
    ⟨fun z => ⟨z, himageQ z.property⟩, continuous_subtype_val.subtype_mk _⟩
  let jI : C(f '' Icc (0 : ℝ) 1, X) := j.comp inc
  have hvalue (t : unitInterval) :
      jI ⟨f t, mem_image_of_mem f t.property⟩ = gamma (squareRimLoop t) := by
    change j ⟨f t, himageQ (mem_image_of_mem f t.property)⟩ = _
    have heq : (⟨f t, himageQ (mem_image_of_mem f t.property)⟩ : a '' Q) =
        ⟨a (squareRimLoop t), mem_image_of_mem a (squareRimLoop t).property⟩ :=
      Subtype.ext (hformula t)
    rw [heq]
    exact hj (squareRimLoop t)
  have hbase :
      jI ⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩ =
        gamma squareRimBase := by
    simpa only [Set.Icc.coe_zero, Path.source] using hvalue (0 : unitInterval)
  let pI := p.cast rfl hbase
  have hloop : (Path.imageIntervalLoop f hf.continuousOn hclosed).map jI.continuous =
      (squareRimLoop.map gamma.continuous).cast hbase hbase := by
    apply Path.ext
    funext t
    exact hvalue t
  have hclass : pI.whiskeredLoopClass
      ((Path.imageIntervalLoop f hf.continuousOn hclosed).map jI.continuous) =
        p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) := by
    rw [hloop]
    rfl
  obtain ⟨K, hspace, G, hG, hK, hdim, v, c, q, hc, hout⟩ :=
    hf.exists_excluded_marked_image_cycle hclosed jI pI J (hclass.symm ▸ houtside)
  have himage : K.space ⊆ a '' Q := hspace.subset.trans himageQ
  refine ⟨K, himage, G, hspace, ?_, hK, hdim, v, c, q, hc, hout⟩
  intro x
  rw [hG x]
  rfl

end PoincareConjecture.M76.Dehn
