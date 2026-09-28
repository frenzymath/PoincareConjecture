import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.EdgeChartHeight
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_triangle_halfInterval
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
    ∃ (B : OpenPartialHomeomorph X V3) (z : V3) (r : ℝ),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      y ∈ B.source ∧ z ≠ B y ∧ 0 < r ∧ r < dist (B y) z ∧
      Metric.ball (B y) r ⊆ B.target ∧
      (B '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ B.source)) ∩
          Metric.ball (B y) r =
        AffineMap.lineMap (B y) z '' Ico (0 : ℝ) (r / dist (B y) z) ∧
      Topology.IsEmbedding (AffineMap.lineMap (B y) z : ℝ → V3) ∧
      ∀ t ∈ Ico (0 : ℝ) (r / dist (B y) z),
        B.symm (AffineMap.lineMap (B y) z t) ∈ g '' segment ℝ p q ↔ t = 0 := by
  classical
  have hat : ({p, q} : Finset E) ⊆ {w, p, q} := by simp
  have ha : ({p, q} : Finset E) ∈ K.faces :=
    K.down_closed ht hat (Finset.insert_nonempty _ _)
  have hypred : y ∈ S ∩ (g '' convexHull ℝ (({p, q} : Finset E) : Set E)) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hy
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hco⟩ := h y hypred
  obtain ⟨hmap, A, hA⟩ := hco {w, p, q} ht hat
  have hA' : EqOn (B ∘ g) A (convexHull ℝ ({w, p, q} : Set E)) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hA
  have hmap' : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) B.source := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hmap
  have hTspace : convexHull ℝ ({w, p, q} : Set E) ⊆ K.space := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using K.convexHull_subset_space ht
  have hsegsub : segment ℝ p q ⊆ convexHull ℝ ({w, p, q} : Set E) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by intro x hx; exact Or.inr hx)
  have hAhull : InjOn A.toAffineMap (convexHull ℝ ({w, p, q} : Set E)) := by
    intro x hx x' hx' heq
    apply hgi (hTspace hx) (hTspace hx')
    apply B.injOn (hmap' hx) (hmap' hx')
    exact (hA' hx).trans (heq.trans (hA' hx').symm)
  have hverts (x : E) (hx : x ∈ ({w, p, q} : Set E)) : B (g x) = A x :=
    hA' (subset_convexHull ℝ _ hx)
  have hpA := hverts p (by simp)
  have hqA := hverts q (by simp)
  have hwA := hverts w (by simp)
  have hsourceEdge : MapsTo g (segment ℝ p q) B.source := hmap'.mono_left hsegsub
  have hedge : (B ∘ g) '' segment ℝ p q = segment ℝ (A p) (A q) := by
    calc
      _ = A.toAffineMap '' segment ℝ p q := image_congr (fun x hx => hA' (hsegsub hx))
      _ = _ := image_segment ℝ A.toAffineMap p q
  have hphysical (x : V3) (hx : x ∈ B.target) :
      B.symm x ∈ g '' segment ℝ p q ↔ x ∈ segment ℝ (A p) (A q) := by
    constructor
    · rintro ⟨u, hu, heq⟩
      rw [← hedge]
      exact ⟨u, hu, by change B (g u) = x; rw [heq, B.right_inv hx]⟩
    · intro hxe
      rw [← hedge] at hxe
      obtain ⟨u, hu, heq⟩ := hxe
      refine ⟨u, hu, ?_⟩
      rw [← heq]
      exact (B.left_inv (hsourceEdge hu)).symm
  have hyseg : B y ∈ segment ℝ (A p) (A q) :=
    (hphysical (B y) (B.map_source hyB)).mp (by simpa only [B.left_inv hyB] using hy.2)
  have hpy : A p ≠ B y := by
    intro heq
    have hyp : g p = y := B.injOn (hsourceEdge (left_mem_segment ℝ p q)) hyB
      (hpA.trans heq)
    exact disjoint_left.mp hSV hy.1 ⟨p, K.face_subset_vertices ha (by simp), hyp⟩
  have hqy : A q ≠ B y := by
    intro heq
    have hyq : g q = y := B.injOn (hsourceEdge (right_mem_segment ℝ p q)) hyB
      (hqA.trans heq)
    exact disjoint_left.mp hSV hy.1 ⟨q, K.face_subset_vertices ha (by simp), hyq⟩
  have hyopen : B y ∈ openSegment ℝ (A p) (A q) :=
    mem_openSegment_of_ne_left_right hpy hqy hyseg
  have hApq : A p ≠ A q := fun heq => hpq (hAhull
    (hsegsub (left_mem_segment ℝ p q)) (hsegsub (right_mem_segment ℝ p q)) heq)
  have hrange : range ((↑) : ({w, p, q} : Finset E) → E) = ({w, p, q} : Set E) := by
    rw [Subtype.range_coe]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  have hind := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull
    (p := ((↑) : ({w, p, q} : Finset E) → E)) (K.indep ht)
    (by rw [hrange]; exact hAhull)
  let ip : ({w, p, q} : Finset E) := ⟨p, by simp⟩
  let iq : ({w, p, q} : Finset E) := ⟨q, by simp⟩
  let iw : ({w, p, q} : Finset E) := ⟨w, by simp⟩
  have hnot := hind.notMem_affineSpan_sdiff iw {ip, iq}
  have hset : ({ip, iq} : Set ({w, p, q} : Finset E)) \ {iw} = {ip, iq} := by
    apply sdiff_eq_left.mpr
    apply disjoint_singleton_right.mpr
    simp [ip, iq, iw, Subtype.ext_iff, hwp, hwq]
  rw [hset, image_pair] at hnot
  change A w ∉ affineSpan ℝ ({A p, A q} : Set V3) at hnot
  have haxis (x : V3) (hx : x ∈ V) (hxe : x ∈ segment ℝ (A p) (A q)) :
      (F.symm x).1 = 0 := by
    have hh := hFL (F.symm x) (by simpa only [F.apply_symm_apply] using hx)
    apply hh.mp
    simpa only [F.apply_symm_apply, Finset.coe_pair, convexHull_pair] using
      (hphysical x (hVB hx)).mpr hxe
  obtain ⟨z, r, hzy, hr, hrdist, hballV, hsection, hemb, hendpoint⟩ :=
    edge_chart_triangle_halfInterval F hF hV hyV hyopen hApq haxis hnot
  have htriangle : (B ∘ g) '' convexHull ℝ ({w, p, q} : Set E) =
      convexHull ℝ ({A w, A p, A q} : Set V3) := by
    calc
      _ = A.toAffineMap '' convexHull ℝ ({w, p, q} : Set E) := image_congr hA'
      _ = _ := by
        rw [A.toAffineMap.image_convexHull, image_insert_eq, image_pair]
        rfl
  have hlocal : (B '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ B.source)) ∩
        Metric.ball (B y) r =
      (convexHull ℝ ({A w, A p, A q} : Set V3) ∩ {x | (F.symm x).2 = 0}) ∩
        Metric.ball (B y) r := by
    ext x
    constructor
    · rintro ⟨⟨v, ⟨⟨hvS, u, hu, huv⟩, hvB⟩, hvx⟩, hxball⟩
      have hxV := hballV hxball
      refine ⟨⟨?_, ?_⟩, hxball⟩
      · rw [← htriangle]
        exact ⟨u, hu, by change B (g u) = x; rw [huv, hvx]⟩
      · have hh := hFS (F.symm x) (by simpa only [F.apply_symm_apply] using hxV)
        apply hh.mp
        simpa only [F.apply_symm_apply, ← hvx, B.left_inv hvB] using hvS
    · rintro ⟨⟨hxt, hxzero⟩, hxball⟩
      have hxV := hballV hxball
      have hxB := hVB hxV
      rw [← htriangle] at hxt
      obtain ⟨u, hu, hux⟩ := hxt
      refine ⟨⟨B.symm x, ⟨⟨?_, ?_⟩, B.map_target hxB⟩, B.right_inv hxB⟩, hxball⟩
      · have hh := hFS (F.symm x) (by simpa only [F.apply_symm_apply] using hxV)
        simpa only [F.apply_symm_apply] using hh.mpr hxzero
      · exact ⟨u, hu, by rw [← hux]; exact (B.left_inv (hmap' hu)).symm⟩
  refine ⟨B, z, r, hB, hyB, hzy, hr, hrdist, hballV.trans hVB,
    hlocal.trans hsection, hemb, ?_⟩
  intro t htpar
  have hxball : AffineMap.lineMap (B y) z t ∈ Metric.ball (B y) r := by
    have hh := hsection.symm.subset (mem_image_of_mem _ htpar)
    exact hh.2
  exact (hphysical _ (hVB (hballV hxball))).trans (hendpoint t htpar)

end PoincareConjecture.M76
