import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLImageWalk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricCyclePolygon











set_option autoImplicit false

open Set

namespace Path

variable {E : Type*} [TopologicalSpace E]




def imageIntervalLoop (f : ℝ → E) (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hclosed : f 1 = f 0) :
    Path (⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩ :
      f '' Icc (0 : ℝ) 1) ⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩ :=
  (intervalIn _ f hc (fun _ hx => mem_image_of_mem f hx)).cast rfl
    (Subtype.ext hclosed.symm)

end Path

namespace SimpleGraph.Walk

private theorem realizePath_copy {V X : Type*} [TopologicalSpace X] {G : SimpleGraph V}
    (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    {u v u' v' : V} (w : G.Walk u v) (hu : u = u') (hv : v = v') :
    realizePath a edge (w.copy hu hv) =
      (realizePath a edge w).cast (congrArg a hu.symm) (congrArg a hv.symm) := by
  subst u'
  subst v'
  rfl

private theorem realizePath_map {V X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {G : SimpleGraph V} (a : V → X)
    (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    (F : C(X, Y)) {u v : V} (w : G.Walk u v) :
    (realizePath a edge w).map F.continuous =
      realizePath (F ∘ a) (fun h => (edge h).map F.continuous) w := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change ((edge h).trans (realizePath a edge w)).map F.continuous = _
    rw [Path.map_trans, ih]
    rfl

end SimpleGraph.Walk

namespace Geometry

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]





theorem FinitePiecewiseAffineOn.exists_excluded_marked_image_cycle
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hclosed : f 1 = f 0) (j : C(f '' Icc (0 : ℝ) 1, X)) {b : X}
    (p : Path b (j ⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩))
    (J : Subgroup (FundamentalGroup X b))
    (houtside : p.whiskeredLoopClass
      ((Path.imageIntervalLoop f hf.continuousOn hclosed).map j.continuous) ∉ J) :
    ∃ (K : SimplicialComplex ℝ E) (hspace : K.space = f '' Icc (0 : ℝ) 1)
      (G : C(K.space, X)),
      (∀ x : K.space, G x = j (Homeomorph.setCongr hspace x)) ∧
      K.faces.Finite ∧ (∀ s ∈ K.faces, s.card ≤ 2) ∧
      ∃ (v : K.vertices) (c : K.vertexAbstractComplex.edgeGraph.Walk v v)
        (q : Path b (G ⟨v, K.vertices_subset_space v.property⟩)),
        c.IsCycle ∧ q.whiskeredLoopClass
          ((K.geometricWalkPath c).map G.continuous) ∉ J := by
  classical
  obtain ⟨K, hzero, hone, hm, hK, hspace, hdim, w, hw⟩ := hf.exists_image_graph_walk
  let H := Homeomorph.setCongr hspace
  let G : C(K.space, X) := j.comp ⟨H, H.continuous⟩
  let a : K.vertices → K.space := fun v => ⟨v, K.vertices_subset_space v.property⟩
  have hend : (⟨f 1, hone⟩ : K.vertices) = ⟨f 0, hzero⟩ := Subtype.ext hclosed
  let W := w.copy rfl hend
  have hcopy : K.geometricWalkPath W =
      (K.geometricWalkPath w).cast rfl (congrArg a hend.symm) :=
    SimpleGraph.Walk.realizePath_copy a (fun h => K.geometricEdgePath h) w rfl hend
  have hloop : (K.geometricWalkPath W).Homotopic
      ((Path.intervalIn K.space f hf.continuousOn hm).cast rfl
        (congrArg a hend.symm)) := by
    rw [hcopy]
    exact hw.pathCast rfl (congrArg a hend.symm)
  have hmap := hloop.map G
  have hsame :
      (((Path.intervalIn K.space f hf.continuousOn hm).cast rfl
        (congrArg a hend.symm)).map G.continuous) =
      (Path.imageIntervalLoop f hf.continuousOn hclosed).map j.continuous := by
    apply Path.ext
    funext z
    rfl
  rw [hsame] at hmap
  have hclass : p.whiskeredLoopClass ((K.geometricWalkPath W).map G.continuous) =
      p.whiskeredLoopClass
        ((Path.imageIntervalLoop f hf.continuousOn hclosed).map j.continuous) :=
    Path.Homotopic.Quotient.eq.mpr
      (((Path.Homotopic.refl p).hcomp hmap).hcomp (Path.Homotopic.refl p.symm))
  have hW : p.whiskeredLoopClass
      (SimpleGraph.Walk.realizePath (G ∘ a)
        (fun h => (K.geometricEdgePath h).map G.continuous) W) ∉ J := by
    rw [← SimpleGraph.Walk.realizePath_map a (fun h => K.geometricEdgePath h) G W]
    exact hclass.symm ▸ houtside
  have hreverse {u v : K.vertices} (h : K.vertexAbstractComplex.edgeGraph.Adj u v) :
      ((K.geometricEdgePath h.symm).map G.continuous).Homotopic
        ((K.geometricEdgePath h).map G.continuous).symm := by
    rw [K.geometricEdgePath_symm h, Path.map_symm]
  obtain ⟨v, c, q, hc, hout⟩ := SimpleGraph.Walk.exists_excluded_realized_cycle
    (G ∘ a) (fun h => (K.geometricEdgePath h).map G.continuous) hreverse J W p hW
  refine ⟨K, hspace, G, fun _ => rfl, hK, hdim, v, c, q, hc, ?_⟩
  rw [← SimpleGraph.Walk.realizePath_map a (fun h => K.geometricEdgePath h) G c] at hout
  exact hout

end Geometry
