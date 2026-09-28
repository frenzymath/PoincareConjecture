import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceCoordinates
import PoincareConjecture.Proofs.M76.PrimeReduction.ActualArcComponents
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_actual_returning_component_coordinates
    (K G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdegree : ∀ v, (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2)
    {v0 v1 v2 : E} (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    (hs : ({v0, v1, v2} : Finset E) ∈ K.faces)
    (hGT : G.space ⊆ convexHull ℝ ({v0, v1, v2} : Set E)) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ)),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (affineSpan ℝ ({v0, v1, v2} : Set E)) ∧
      F (0, 0) = v0 ∧ F (1, 0) = v1 ∧ F (0, 1) = v2 ∧
      F '' convexHull ℝ (range rightTriangle) = convexHull ℝ ({v0, v1, v2} : Set E) ∧
      F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ ({v0, v1} : Set E) ∧
      ∀ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent),
        (∃ v : C, (G.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) →
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
            intrinsicFrontier ℝ (convexHull ℝ ({v0, v1, v2} : Set E)) =
          Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
            (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} →
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
            (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} ⊆
          convexHull ℝ ({v0, v1} : Set E) →
        ∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
          let q : Fin (n + 2) → E := fun i => ((e i).val : E)
          let p : Fin (n + 2) → ℝ × ℝ := R ∘ q
          C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) = Polygon.pathCarrier q ∧
          IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
            {q 0, q (Fin.last (n + 1))} ∧
          Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
              (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} =
            {q 0, q (Fin.last (n + 1))} ∧
          Function.Injective p ∧
          (∀ i j : Fin (n + 1),
            segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
              convexHull ℝ (({p i.castSucc, p i.succ} : Set (ℝ × ℝ)) ∩
                {p j.castSucc, p j.succ})) ∧
          (∀ i, 0 ≤ (p i).2) ∧
          Polygon.pathCarrier p ∩ {z : ℝ × ℝ | z.2 = 0} =
            {p 0, p (Fin.last (n + 1))} ∧
          R '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) = Polygon.pathCarrier p ∧
          F '' Polygon.pathCarrier p = C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := by
  classical
  obtain ⟨F, R, hRF, hFR, hF0, hF1, hF2, hface, hedge, hRface, hzero⟩ :=
    K.exists_returning_face_coordinates h01 h02 h12 (by
      convert hs using 1
      ext x
      simp)
  have hFRh (x : E) (hx : x ∈ convexHull ℝ ({v0, v1, v2} : Set E)) : F (R x) = x :=
    hFR (convexHull_subset_affineSpan _ hx)
  have hRi : InjOn R (convexHull ℝ ({v0, v1, v2} : Set E)) := by
    intro x hx y hy hxy
    exact (hFRh x hx).symm.trans ((congrArg F hxy).trans (hFRh y hy))
  have hedgefront : convexHull ℝ ({v0, v1} : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ ({v0, v1, v2} : Set E)) := by
    have hsub : ({v0, v1} : Finset E) ⊂ {v0, v1, v2} :=
      Finset.ssubset_iff_subset_ne.mpr ⟨by simp [Finset.subset_iff], by
      intro heq
      have : v2 ∈ ({v0, v1} : Finset E) := heq ▸ (by simp)
      simp [h02.symm, h12.symm] at this⟩
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (K.indep hs).convexHull_subset_intrinsicFrontier hsub
  refine ⟨F, R, hRF, hFR, hF0, hF1, hF2, hface, hedge, ?_⟩
  intro C hleaf hfront hreturn
  obtain ⟨n, e, hcarrier, hball, hends, hadj⟩ :=
    G.exists_actual_component_interval hG hdegree C hleaf
  let q : Fin (n + 2) → E := fun i => ((e i).val : E)
  let p : Fin (n + 2) → ℝ × ℝ := R ∘ q
  have hqT (i : Fin (n + 2)) : q i ∈ convexHull ℝ ({v0, v1, v2} : Set E) :=
    hGT (G.subset_space (e i).val.property (by simp [q]))
  have hqinj : Function.Injective q :=
    (Subtype.val_injective.comp Subtype.val_injective).comp e.injective
  have hsegT (i : Fin (n + 1)) : segment ℝ (q i.castSucc) (q i.succ) ⊆
      convexHull ℝ ({v0, v1, v2} : Set E) :=
    (convex_convexHull ℝ _).segment_subset (hqT _) (hqT _)
  have hpathT : Polygon.pathCarrier q ⊆ convexHull ℝ ({v0, v1, v2} : Set E) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hsegT i hi
  have hpathR : R '' Polygon.pathCarrier q = Polygon.pathCarrier p := by
    simp only [Polygon.pathCarrier, image_iUnion]
    apply iUnion_congr
    intro i
    exact image_segment ℝ R.toAffineMap (q i.castSucc) (q i.succ)
  have hpathF : F '' Polygon.pathCarrier p = Polygon.pathCarrier q := by
    rw [← hpathR, ← image_comp]
    exact (image_congr (fun x hx => hFRh x (hpathT hx))).trans (image_id _)
  have haxisiff (x : E) (hx : x ∈ convexHull ℝ ({v0, v1, v2} : Set E)) :
      (R x).2 = 0 ↔ x ∈ convexHull ℝ ({v0, v1} : Set E) := by
    constructor
    · intro hx0
      have hright := (mem_right_region_iff (R x)).mp (hRface.subset ⟨x, hx, rfl⟩)
      have hxseg : R x ∈ segment ℝ (0, 0) (1, 0) := by
        rw [segment_eq_image_lineMap]
        refine ⟨(R x).1, ⟨hright.1, by linarith [hright.2.2]⟩, ?_⟩
        apply Prod.ext <;> simp [AffineMap.lineMap_apply, hx0]
      exact hedge.subset ⟨R x, hxseg, hFRh x hx⟩
    · intro hxedge
      exact hzero (R x) (by rw [hFRh x hx]; exact hxedge)
  have haxis : Polygon.pathCarrier p ∩ {z : ℝ × ℝ | z.2 = 0} =
      {p 0, p (Fin.last (n + 1))} := by
    ext z
    constructor
    · rintro ⟨hz, hz0⟩
      obtain ⟨x, hx, rfl⟩ := hpathR.symm.subset hz
      have hxedge := (haxisiff x (hpathT hx)).mp hz0
      have hxends := hends.subset (hfront.subset
        ⟨hcarrier.symm.subset hx, hedgefront hxedge⟩)
      rcases hxends with hx0 | hxlast
      · exact Or.inl (congrArg R hx0)
      · exact Or.inr (congrArg R hxlast)
    · rintro (rfl | rfl)
      · exact ⟨Polygon.vertex_mem_pathCarrier p 0,
          (haxisiff _ (hqT 0)).mpr (hreturn (hends.symm.subset (Or.inl rfl)))⟩
      · exact ⟨Polygon.vertex_mem_pathCarrier p _,
          (haxisiff _ (hqT _)).mpr (hreturn (hends.symm.subset (Or.inr rfl)))⟩
  refine ⟨n, e, hcarrier, hball, hends, ?_, ?_, ?_, haxis, ?_, ?_⟩
  · intro i j hij
    exact hqinj (hRi (hqT i) (hqT j) hij)
  · intro i j x hx
    have hi := (image_segment ℝ R.toAffineMap (q i.castSucc) (q i.succ)).symm.subset hx.1
    have hj := (image_segment ℝ R.toAffineMap (q j.castSucc) (q j.succ)).symm.subset hx.2
    obtain ⟨y, hy, hyx⟩ := hi
    obtain ⟨z, hz, hzx⟩ := hj
    have hyz : y = z := hRi (hsegT i hy) (hsegT j hz) (hyx.trans hzx.symm)
    subst z
    have hsegment := G.actual_edgeGraph_segment_intersection
      ((hadj _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
      ((hadj _ _).mpr ⟨j, Or.inl ⟨rfl, rfl⟩⟩)
    have hyh := hsegment ⟨hy, hz⟩
    have hximage : x ∈ R '' convexHull ℝ
        (({q i.castSucc, q i.succ} : Set E) ∩ {q j.castSucc, q j.succ}) :=
      ⟨y, hyh, hyx⟩
    have hximage' := (R.toAffineMap.image_convexHull _).subset hximage
    apply convexHull_mono (s := R ''
      (({q i.castSucc, q i.succ} : Set E) ∩ {q j.castSucc, q j.succ})) ?_ hximage'
    rintro z ⟨w, ⟨hwi, hwj⟩, rfl⟩
    constructor <;> simp only [mem_insert_iff, mem_singleton_iff] at *
    · rcases hwi with rfl | rfl <;> simp [q]
    · rcases hwj with rfl | rfl <;> simp [q]
  · intro i
    exact ((mem_right_region_iff (p i)).mp (hRface.subset ⟨q i, hqT i, rfl⟩)).2.1
  · rw [hcarrier]
    exact hpathR
  · exact hpathF.trans hcarrier.symm

end Geometry.SimplicialComplex
