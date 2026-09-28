import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.ConstructedAxisAmbientMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PhysicalReturningFaceProtection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.FinitePLReturningBigon
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceRegion
import PoincareConjecture.Proofs.M76.PrimeReduction.FaceNormalExtension









set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Axis" => (Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ)




theorem exists_original_face_axis_move_with_edge_support
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {K N : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s a : Finset E} (hs : s ∈ K.faces) (ha : a ∈ K.faces)
    (hs3 : s.card = 3) (ha2 : a.card = 2) (has : a ⊆ s)
    {u : E} (hu : u ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
    (huZ : g u ∉ Z)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F)
    (hFR : EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))))
    (hface : F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (A '' (s : Set E)))
    (hbase : F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (A '' (a : Set E)))
    {W : Set P2} {p q c d : P2}
    (hW : IsFinitePLBallPair ℝ W {p, q}) (hpq : p.1 < q.1)
    (hp : p.2 = 0) (hq : q.2 = 0)
    (hup : ∀ z ∈ W, 0 ≤ z.2) (hWaxis : W ∩ Axis = {p, q})
    (hFW : F '' W ⊆ A '' (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
      intrinsicInterior ℝ (convexHull ℝ (a : Set E))))
    (G : SimplicialComplex ℝ V3) {Sigma : Set X}
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (hphysical : Q.symm '' G.space = Sigma ∩ (g '' convexHull ℝ (s : Set E)))
    (havoid : Disjoint W (R '' G.space))
    (hcontact : (R '' G.space) ∩ segment ℝ p q = {c, d}) (hcd : c ≠ d)
    (hfinite : ((g '' convexHull ℝ (a : Set E)) ∩ Sigma).Finite) :
    let j : P2 → X := fun z => Q.symm (F z)
    let edge := g '' convexHull ℝ (a : Set E)
    ∃ (H : X ≃ₜ X) (C U : Set X),
      IsOpen U ∧ IsCompact C ∧ C ⊆ U ∧
      Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        Disjoint U (g '' convexHull ℝ (t : Set E))) ∧
      (∀ y ∉ C, H y = y) ∧ (∀ y ∉ U, H y = y) ∧
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id (edge \ j '' segment ℝ p q) ∧
      H '' edge = (edge \ j '' segment ℝ p q) ∪ j '' W ∧
      edge ∩ (H.symm '' Sigma) = (edge ∩ Sigma) \ {j c, j d} ∧
      (edge ∩ (H.symm '' Sigma)).ncard = (edge ∩ Sigma).ncard - 2 ∧
      EqOn H id Z ∧ EqOn H id (g '' K.vertices) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        (g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' Sigma) =
          (g '' convexHull ℝ (t : Set E)) ∩ Sigma) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        ((g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' Sigma)).ncard =
          ((g '' convexHull ℝ (t : Set E)) ∩ Sigma).ncard) ∧
      edge ∩ C ⊆ j '' segment ℝ p q ∧
      Disjoint C (edge ∩ (H.symm '' Sigma)) := by
  classical
  let j : P2 → X := fun z => Q.symm (F z)
  let edge := g '' convexHull ℝ (a : Set E)
  let L := intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
    intrinsicInterior ℝ (convexHull ℝ (a : Set E))
  have hLa : convexHull ℝ (a : Set E) ⊆ convexHull ℝ (s : Set E) := convexHull_mono has
  have hLs : L ⊆ convexHull ℝ (s : Set E) := by
    rintro x (hx | hx)
    · exact intrinsicInterior_subset hx
    · exact hLa (intrinsicInterior_subset hx)
  have hLconvex : Convex ℝ L :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_union_of_subset
      (convex_convexHull ℝ (a : Set E)) hLa
  have hAi : A '' convexHull ℝ (s : Set E) = convexHull ℝ (A '' (s : Set E)) :=
    A.toAffineMap.image_convexHull _
  have hAia : A '' convexHull ℝ (a : Set E) = convexHull ℝ (A '' (a : Set E)) :=
    A.toAffineMap.image_convexHull _
  have htarget {y : V3} (hy : y ∈ convexHull ℝ (A '' (s : Set E))) : y ∈ Q.target := by
    obtain ⟨x, hx, rfl⟩ := hAi.symm.subset hy
    rw [← hA hx]
    exact Q.mapsTo (hmap hx)
  have hinverse {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) : Q.symm (A x) = g x := by
    rw [← hA hx]
    exact Q.left_inv (hmap hx)
  have hjface {z : P2} (hz : F z ∈ convexHull ℝ (A '' (s : Set E))) :
      j z ∈ g '' convexHull ℝ (s : Set E) := by
    obtain ⟨x, hx, heq⟩ := hAi.symm.subset hz
    exact ⟨x, hx, (hinverse hx).symm.trans (congrArg Q.symm heq)⟩
  have hscene {z : P2} (hz : F z ∈ convexHull ℝ (A '' (s : Set E))) :
      j z ∈ Sigma ↔ z ∈ R '' G.space := by
    constructor
    · intro hzS
      obtain ⟨y, hy, heq⟩ := hphysical.symm.subset ⟨hzS, hjface hz⟩
      have hyz : y = F z := Q.symm.injOn (htarget (hGT hy)) (htarget hz) heq
      exact ⟨y, hy, hyz ▸ hRF z⟩
    · rintro ⟨y, hy, rfl⟩
      have heq : F (R y) = y := hFR (convexHull_subset_affineSpan _ (hGT hy))
      exact (hphysical.subset ⟨y, hy, (congrArg Q.symm heq).symm⟩).1
  obtain ⟨U, hU, hLU, hUZ, hUV, hUother⟩ :=
    Geometry.SimplicialComplex.exists_physical_returning_face_neighborhood
      hK hNK g hgc hgi hZ hmark hs ha hs3 ha2 has hu huZ
  have hpq' : p ≠ q := fun h => hpq.ne (congrArg Prod.fst h)
  obtain ⟨n, P, _, _, _, _, hB, _, _, hBconvex⟩ :=
    exists_finite_pl_returning_bigon hW hpq' hup hWaxis
  have hBL : MapsTo F (closure P.inside) (A '' L) :=
    hBconvex (F ⁻¹' (A '' L))
      ((hLconvex.affine_image A.toAffineMap).affine_preimage F.toAffineMap)
      (fun z hz => hFW ⟨z, hz, rfl⟩)
  obtain ⟨T, hTzero, hTinv, _⟩ := F.exists_normal_extension hRF.injective (by simp)
  have hzero : ∀ z ∈ closure P.inside,
      T (z, 0) ∈ Q.target ∧ Q.symm (T (z, 0)) ∈ U := by
    intro z hz
    obtain ⟨x, hx, heq⟩ := hBL hz
    rw [hTzero, ← heq]
    exact ⟨htarget (hAi.subset ⟨x, hLs hx, rfl⟩),
      (hinverse (hLs hx)).symm ▸ hLU ⟨x, hx, rfl⟩⟩
  have hwB : segment ℝ p q ⊆ closure P.inside := subset_union_right.trans hB.1
  have hWB : W ⊆ closure P.inside := subset_union_left.trans hB.1
  have hFtri {z : P2} (hz : z ∈ closure P.inside) :
      F z ∈ convexHull ℝ (A '' (s : Set E)) :=
    hAi.subset ((image_mono hLs) (hBL hz))
  have hjinj : InjOn j (closure P.inside) := by
    intro x hx y hy hxy
    exact hRF.injective (Q.symm.injOn (htarget (hFtri hx)) (htarget (hFtri hy)) hxy)
  have hc : c ∈ segment ℝ p q := (hcontact.symm.subset (by simp)).2
  have hd : d ∈ segment ℝ p q := (hcontact.symm.subset (by simp)).2
  have hjcd : j c ≠ j d := fun h => hcd (hjinj (hwB hc) (hwB hd) h)
  have havoid' : Disjoint W ((fun z : P2 => Q.symm (T (z, 0))) ⁻¹' Sigma) := by
    apply disjoint_left.mpr
    intro z hz hzs
    apply disjoint_left.mp havoid hz
    apply (hscene (hFtri (hWB hz))).mp
    change Q.symm (T (z, 0)) ∈ Sigma at hzs
    simpa only [hTzero] using hzs
  have hcontact' : ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ p q) ∩ Sigma =
      {j c, j d} := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzS⟩
      have hzG : z ∈ R '' G.space := (hscene (hFtri (hwB hz))).mp
        (by simpa only [hTzero] using hzS)
      have hzcd := hcontact.subset ⟨hzG, hz⟩
      rcases hzcd with hzcd | hzcd
      · exact Or.inl (by simpa only [hTzero] using congrArg j hzcd)
      · exact Or.inr (by simpa only [hTzero, mem_singleton_iff] using congrArg j hzcd)
    · intro hx
      have hend {z : P2} (hz : z ∈ ({c, d} : Set P2)) :
          j z ∈ ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ p q) ∩ Sigma := by
        have hzc := hcontact.symm.subset hz
        exact ⟨⟨z, hzc.2, by simp only [hTzero]; rfl⟩,
          (hscene (hFtri (hwB hzc.2))).mpr hzc.1⟩
      rcases hx with hx | hx
      · exact hx ▸ hend (by simp)
      · exact hx ▸ hend (by simp)
  have hwbase : segment ℝ p q ⊆ segment ℝ (0, 0) (1, 0) := by
    have hend {z : P2} (hz : z ∈ W) (hz0 : z.2 = 0) : z ∈ segment ℝ (0, 0) (1, 0) := by
      have hzT := hface.symm.subset (hFtri (hWB hz))
      obtain ⟨y, hy, heq⟩ := hzT
      have hzy : z = y := (hRF.injective heq).symm
      subst y
      have hh := (mem_right_region_iff z).mp hy
      apply (PlanarSegment.mem_segment_iff (by norm_num : (0 : ℝ) ≠ 1)).mpr
      exact ⟨by simpa only [uIcc_of_le zero_le_one] using ⟨hh.1, by linarith [hh.2.2]⟩,
        by simpa [PlanarSegment.height] using hz0⟩
    exact (convex_segment (𝕜 := ℝ) (0, 0) (1, 0)).segment_subset
      (hend (hW.1 (by simp)) hp) (hend (hW.1 (by simp)) hq)
  have hwedge : ((fun z : P2 => Q.symm (T (z, 0))) '' segment ℝ p q) ⊆ edge := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, heq⟩ := hAia.symm.subset (hbase.subset ⟨z, hwbase hz, rfl⟩)
    refine ⟨x, hx, (hinverse (hLa hx)).symm.trans ?_⟩
    change Q.symm (A x) = Q.symm (T (z, 0))
    rw [hTzero, ← heq]
  have hedgeAxis : ∀ x ∈ edge ∩ Q.source,
      (T.symm (Q x)).1 ∈ Axis ∧ (T.symm (Q x)).2 = 0 := by
    rintro x ⟨⟨y, hy, rfl⟩, _⟩
    obtain ⟨z, hz, heq⟩ := hbase.symm.subset (hAia.subset ⟨y, hy, rfl⟩)
    have hAy : Q (g y) = A y := hA (hLa hy)
    rw [hAy, ← heq, hTinv]
    exact ⟨Polygon.segment_subset_returning_axis rfl rfl hz, rfl⟩
  let Other := {t : Finset E // t ∈ K.faces ∧ t.card ≤ 2 ∧ t ≠ a}
  let untouched : Other → Set X := fun t => g '' convexHull ℝ (t.val : Set E)
  have hprotected : ∀ t, Disjoint U (untouched t) :=
    fun t => hUother t.val t.property.1 t.property.2.1 t.property.2.2
  obtain ⟨D, H, C, _, _, _, _, _, _, _, _, _, hDaxis, hC, hCU, hcoords, hHC, hHU,
      hHPL, hHinv, hfix, himage, hexact, hdrop, hother, hothercard⟩ :=
    exists_original_constructed_axis_ambient_move e he Q hQ T hW hpq hp hq hup hWaxis
      (by simpa only [union_comm] using hB) hU hzero havoid' hcontact' hjcd
      hwedge hedgeAxis hfinite untouched hprotected
  obtain ⟨r, _, hCr, hprism⟩ := hcoords
  have hsupport : edge ∩ C ⊆ j '' segment ℝ p q := by
    rw [hCr]
    simpa only [hTzero] using
      coarse_edge_inter_prism_support_subset_axis Q T hDaxis hprism hedgeAxis
  have hnew : Disjoint C (edge ∩ (H.symm '' Sigma)) := by
    apply disjoint_left.mpr
    intro x hxC hxnew
    have hxold := hexact.subset hxnew
    have hxpair : x ∈ ({j c, j d} : Set X) := hcontact'.subset
      ⟨by simpa only [hTzero] using hsupport ⟨hxnew.1, hxC⟩, hxold.1.2⟩
    exact hxold.2 hxpair
  refine ⟨H, C, U, hU, hC, hCU, hUZ, hUV, hUother, hHC, hHU, hHPL, hHinv,
    ?_, ?_, hexact, hdrop, ?_, ?_, ?_, ?_, hsupport, hnew⟩
  · simpa only [hTzero] using hfix
  · simpa only [hTzero] using himage
  · exact fun x hx => hHU x (fun hxU => disjoint_left.mp hUZ hxU hx)
  · exact fun x hx => hHU x (fun hxU => disjoint_left.mp hUV hxU hx)
  · intro t ht ht2 hta
    exact hother ⟨t, ht, ht2, hta⟩
  · intro t ht ht2 hta
    exact hothercard ⟨t, ht, ht2, hta⟩



theorem exists_original_face_axis_move
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {K N : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s a : Finset E} (hs : s ∈ K.faces) (ha : a ∈ K.faces)
    (hs3 : s.card = 3) (ha2 : a.card = 2) (has : a ⊆ s)
    {u : E} (hu : u ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
    (huZ : g u ∉ Z)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F)
    (hFR : EqOn (F ∘ R) id (affineSpan ℝ (A '' (s : Set E))))
    (hface : F '' convexHull ℝ (range rightTriangle) = convexHull ℝ (A '' (s : Set E)))
    (hbase : F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ (A '' (a : Set E)))
    {W : Set P2} {p q c d : P2}
    (hW : IsFinitePLBallPair ℝ W {p, q}) (hpq : p.1 < q.1)
    (hp : p.2 = 0) (hq : q.2 = 0)
    (hup : ∀ z ∈ W, 0 ≤ z.2) (hWaxis : W ∩ Axis = {p, q})
    (hFW : F '' W ⊆ A '' (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
      intrinsicInterior ℝ (convexHull ℝ (a : Set E))))
    (G : SimplicialComplex ℝ V3) {Sigma : Set X}
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (hphysical : Q.symm '' G.space = Sigma ∩ (g '' convexHull ℝ (s : Set E)))
    (havoid : Disjoint W (R '' G.space))
    (hcontact : (R '' G.space) ∩ segment ℝ p q = {c, d}) (hcd : c ≠ d)
    (hfinite : ((g '' convexHull ℝ (a : Set E)) ∩ Sigma).Finite) :
    let j : P2 → X := fun z => Q.symm (F z)
    let edge := g '' convexHull ℝ (a : Set E)
    ∃ (H : X ≃ₜ X) (C U : Set X),
      IsOpen U ∧ IsCompact C ∧ C ⊆ U ∧
      Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        Disjoint U (g '' convexHull ℝ (t : Set E))) ∧
      (∀ y ∉ C, H y = y) ∧ (∀ y ∉ U, H y = y) ∧
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id (edge \ j '' segment ℝ p q) ∧
      H '' edge = (edge \ j '' segment ℝ p q) ∪ j '' W ∧
      edge ∩ (H.symm '' Sigma) = (edge ∩ Sigma) \ {j c, j d} ∧
      (edge ∩ (H.symm '' Sigma)).ncard = (edge ∩ Sigma).ncard - 2 ∧
      EqOn H id Z ∧ EqOn H id (g '' K.vertices) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        (g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' Sigma) =
          (g '' convexHull ℝ (t : Set E)) ∩ Sigma) ∧
      (∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        ((g '' convexHull ℝ (t : Set E)) ∩ (H.symm '' Sigma)).ncard =
          ((g '' convexHull ℝ (t : Set E)) ∩ Sigma).ncard) := by
  obtain ⟨H, C, U, hU, hC, hCU, hUZ, hUV, hUother, hHC, hHU, hHPL, hHinv,
      hfix, himage, hexact, hdrop, hZfix, hVfix, hother, hothercard, _, _⟩ :=
    exists_original_face_axis_move_with_edge_support e he hK hNK g hgc hgi hZ hmark
      hs ha hs3 ha2 has hu huZ Q hQ A hmap hA F R hRF hFR hface hbase
      hW hpq hp hq hup hWaxis hFW G hGT hphysical havoid hcontact hcd hfinite
  exact ⟨H, C, U, hU, hC, hCU, hUZ, hUV, hUother, hHC, hHU, hHPL, hHinv,
    hfix, himage, hexact, hdrop, hZfix, hVfix, hother, hothercard⟩

end PoincareConjecture.M76
