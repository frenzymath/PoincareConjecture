import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineGraphWalkPaths

set_option autoImplicit false

open Set
open scoped unitInterval

namespace Path

variable {E : Type*} [TopologicalSpace E]

def intervalIn (s : Set E) (f : ℝ → E)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hm : MapsTo f (Icc (0 : ℝ) 1) s) :
    Path (⟨f 0, hm ⟨le_rfl, zero_le_one⟩⟩ : s)
      ⟨f 1, hm ⟨zero_le_one, le_rfl⟩⟩ where
  toFun t := ⟨f t, hm t.property⟩
  continuous_toFun :=
    (hc.comp_continuous continuous_subtype_val (fun t => t.property)).subtype_mk _
  source' := rfl
  target' := rfl

end Path

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

private theorem geometricWalkPath_copy {a b c d : K.vertices}
    (w : K.vertexAbstractComplex.edgeGraph.Walk a b) (ha : a = c) (hb : b = d) :
    K.geometricWalkPath (w.copy ha hb) =
      (K.geometricWalkPath w).cast
        (congrArg (fun x : K.vertices =>
          (⟨x, K.vertices_subset_space x.property⟩ : K.space)) ha.symm)
        (congrArg (fun x : K.vertices =>
          (⟨x, K.vertices_subset_space x.property⟩ : K.space)) hb.symm) := by
  subst c
  subst d
  rfl

theorem exists_partitioned_geometric_walk
    (hK : K.faces.Finite) (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (f : ℝ → E) (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hm : MapsTo f (Icc (0 : ℝ) 1) K.space)
    (hzero : f 0 ∈ K.vertices) (hone : f 1 ∈ K.vertices)
    {n : ℕ} (t : Fin (n + 2) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last (n + 1)) = 1)
    (hv : ∀ i, f (t i) ∈ K.vertices)
    (hformula : ∀ i : Fin (n + 1), ∃ A : ℝ →ᴬ[ℝ] E,
      EqOn f A (Icc (t i.castSucc) (t i.succ))) :
    ∃ w : K.vertexAbstractComplex.edgeGraph.Walk ⟨f 0, hzero⟩ ⟨f 1, hone⟩,
      (K.geometricWalkPath w).Homotopic (Path.intervalIn K.space f hc hm) := by
  classical
  have hparam (i : Fin (n + 2)) : t i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← ht0]
      exact ht.monotone (Fin.zero_le i)
    · rw [← ht1]
      exact ht.monotone (Fin.le_last i)
  let τ : Fin (n + 2) → unitInterval := fun i => ⟨t i, hparam i⟩
  let r : Fin (n + 2) → K.vertices := fun i => ⟨f (t i), hv i⟩
  let j : K.vertices → K.space := fun x => ⟨x, K.vertices_subset_space x.property⟩
  let p := Path.intervalIn K.space f hc hm
  have hpiece (i : Fin (n + 1)) :
      ∃ w : K.vertexAbstractComplex.edgeGraph.Walk (r i.castSucc) (r i.succ),
        (K.geometricWalkPath w).Homotopic (p.subpath (τ i.castSucc) (τ i.succ)) := by
    obtain ⟨A, hA⟩ := hformula i
    have hlt : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
    have hlocal : Icc (t i.castSucc) (t i.succ) ⊆ Icc (0 : ℝ) 1 := fun x hx =>
      ⟨(hparam _).1.trans hx.1, hx.2.trans (hparam _).2⟩
    have hAm : MapsTo A (Icc (t i.castSucc) (t i.succ)) K.space := fun x hx =>
      hA hx ▸ hm (hlocal hx)
    apply K.exists_geometric_walk_homotopic_of_affine hK hdim A hlt hAm
      (a := r i.castSucc) (b := r i.succ)
      (hA (left_mem_Icc.mpr hlt.le)) (hA (right_mem_Icc.mpr hlt.le))
      (p.subpath (τ i.castSucc) (τ i.succ))
    intro z
    have hz : ((Icc.convexComb (τ i.castSucc) (τ i.succ) z : unitInterval) : ℝ) ∈
        Icc (t i.castSucc) (t i.succ) :=
      (convex_Icc (t i.castSucc) (t i.succ))
        (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le)
        (sub_nonneg.mpr z.property.2) z.property.1 (sub_add_cancel _ _)
    change f (Icc.convexComb (τ i.castSucc) (τ i.succ) z : ℝ) ∈ _
    rw [hA hz]
    have himage := image_segment ℝ A.toAffineMap (t i.castSucc) (t i.succ)
    rw [segment_eq_Icc hlt.le] at himage
    exact himage.subset (mem_image_of_mem A hz)
  choose w hw using hpiece
  let W := SimpleGraph.Walk.concatSequence r w
  have hreal : (K.geometricWalkPath W).Homotopic
      (Path.concat (j ∘ r) (fun i => K.geometricWalkPath (w i))) :=
    Path.Homotopic.Quotient.eq.mp
      (SimpleGraph.Walk.realizePath_concatSequence j (fun h => K.geometricEdgePath h) r w)
  have hsteps := Path.Homotopic.concat_hcomp (p ∘ τ)
    (fun i => K.geometricWalkPath (w i))
    (fun i => p.subpath (τ i.castSucc) (τ i.succ)) hw
  have hjoined : (K.geometricWalkPath W).Homotopic
      (p.subpath (τ 0) (τ (Fin.last (n + 1)))) :=
    hreal.trans (hsteps.trans (Path.Homotopic.concat_subpath p τ))
  have hr0 : r 0 = ⟨f 0, hzero⟩ := Subtype.ext (congrArg f ht0)
  have hr1 : r (Fin.last (n + 1)) = ⟨f 1, hone⟩ := Subtype.ext (congrArg f ht1)
  refine ⟨W.copy hr0 hr1, ?_⟩
  rw [K.geometricWalkPath_copy W hr0 hr1]
  have hfinal := hjoined.pathCast (congrArg j hr0.symm) (congrArg j hr1.symm)
  have heq : (p.subpath (τ 0) (τ (Fin.last (n + 1)))).cast
      (congrArg j hr0.symm) (congrArg j hr1.symm) = p := by
    apply Path.ext
    funext z
    change p (Icc.convexComb (τ 0) (τ (Fin.last (n + 1))) z) = p z
    have hτ0 : τ 0 = 0 := Subtype.ext ht0
    have hτ1 : τ (Fin.last (n + 1)) = 1 := Subtype.ext ht1
    rw [hτ0, hτ1]
    simp
  erw [heq] at hfinal
  exact hfinal

end Geometry.SimplicialComplex
