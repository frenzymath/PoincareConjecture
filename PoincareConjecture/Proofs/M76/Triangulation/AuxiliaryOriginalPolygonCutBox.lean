import PoincareConjecture.Proofs.M76.Triangulation.ActualOriginalCutBox
import PoincareConjecture.Proofs.M76.Triangulation.RadialCutEventLink
import PoincareConjecture.Proofs.M76.Mathlib.PairedPositiveApexLinearGerms
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCutLinkAccumulation
import PoincareConjecture.Proofs.M76.Mathlib.MinimalFaceRadialTransport












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}






theorem exists_auxiliary_original_polygon_cut_box
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (M : SimplicialComplex ℝ E) (hM : M.faces.Finite) (hMK : M.space = K.space)
    (hpure : ∀ s ∈ M.faces, ∃ t ∈ M.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ M.faces, s.card = 2 →
      {t : Finset E | t ∈ M.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hvertexM : (0 : E) ∈ M.vertices)
    (hconn : (M.link 0).vertexAbstractComplex.edgeGraph.Connected)
    (hdim : Module.finrank ℝ E = 3) (A : E →ₗ[ℝ] ℝ)
    (hpos : (0 : E) ∈ closure (K.space ∩ {x | 0 < A x}))
    (hneg : (0 : E) ∈ closure (K.space ∩ {x | A x < 0}))
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = 0})
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (hvertex : P (finRotate (n + 3) i) = 0)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hdisj : Disjoint C (M.link 0).space)
    (hlocal : M.space ∩ C = (M.closedStar 0).space ∩ C)
    (hfaceC : ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
      (0 : E) ∈ convexHull ℝ (s : Set E))
    {ι : Type*} [Finite ι] [Nonempty ι] (Z : ι → E →ₗ[ℝ] ℝ)
    (hZ : ∀ j, Z j ≠ 0) (hrep : C = {x | ∀ j, Z j x ≤ 1})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJC : J.space = frontier C)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ K.faces) (hcard : ∀ j, (s j).card = 3)
    (ha : ∀ j, P.edgeCut t (if j then finRotate (n + 3) i else i) ∈
      intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (haC : ∀ j : Bool, P.edgeCut t (if j then finRotate (n + 3) i else i) ∈ interior C)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hfzero : ∀ j, f j 0 = P.edgeCut t (if j then finRotate (n + 3) i else i))
    {R : ℝ} (hR : 0 < R)
    (harc : ∀ j x, x ∈ box R →
      (f j x ∈ P.cutArc t (if j then finRotate (n + 3) i else i) ↔
        x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2))
    (hfheight : ∀ j x, A (f j x) = x.1.1)
    (hsurface : ∀ j x, x ∈ box R → (f j x ∈ K.space ↔ x.2 = 0))
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (hinward : ∀ j x, x ∈ box R → x.1.1 = 0 → (f j x ∈ d ↔ 0 ≤ x.2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ))
      (F : ((ℝ × ℝ) × ℝ) → E) (k : Bool → ℝ),
      δ ∈ Ioo 0 ε ∧ δ < R ∧ (∀ j, 0 < k j) ∧ H.source = interior C ∧
      F = H.symm ∘ longitudinalPrismCoordinates δ (-1) 1 ∧
      F '' box δ ⊆ H.source ∧
      FinitePiecewiseAffineOn F (box δ) ∧ InjOn F (box δ) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (F '' box δ) (F '' boxBoundary δ) ∧
      (∀ x ∈ box δ, A (F x) = x.1.1) ∧
      (∀ x ∈ box δ, F x ∈ K.space ↔ x.2 = 0) ∧
      (∀ j u z, u ∈ Icc (-δ) δ → z ∈ Icc (-δ) δ →
        F ((u, if j then δ else -δ), z) = f j ((u, 0), z)) ∧
      (∀ j, f j '' box δ ⊆ H.source) ∧
      (∀ j x, x ∈ box δ →
        H (f j x) = ((x.1.1, (if j then 1 else -1) + k j * x.1.2), x.2)) ∧
      (∀ x ∈ box δ, H (F x) = longitudinalPrismCoordinates δ (-1) 1 x) ∧
      F '' (({0} ×ˢ Icc (-δ) δ) ×ˢ {0}) = P.cutArc t i := by
  classical
  letI := Fintype.ofFinite ι
  let a (j : Bool) : E := P.edgeCut t (if j then finRotate (n + 3) i else i)
  let σ (j : Bool) : ℝ := if j then 1 else -1
  have hσneg : σ false < 0 := by norm_num [σ]
  have hσpos : 0 < σ true := by norm_num [σ]
  have hσne (j : Bool) : σ j ≠ 0 := by cases j <;> norm_num [σ]
  obtain ⟨k, L, _, hL⟩ :=
    P.exists_paired_positive_apex_linear_germs hP hinj t ht i hvertex
      f hfzero hR harc A hfheight σ hσneg hσpos
  simp only [forall_and] at hL
  rcases hL with ⟨hk, _, _, hLa0, hfull, _, hLheight, hlateral⟩
  have hLa (j : Bool) : L j (a j) = ((0, σ j), 0) := by
    change L j (P.edgeCut t (if j then finRotate (n + 3) i else i)) = _
    rw [← hfzero j]
    exact hLa0 j
  have hflast (j : Bool) (x : (ℝ × ℝ) × ℝ) : (L j (f j x)).2 = x.2 := by
    have h := congrArg Prod.snd (hfull j x)
    exact h
  have hA : A ≠ 0 := by
    intro hz
    have hh := hfheight false ((1, 0), 0)
    rw [hz, LinearMap.zero_apply] at hh
    norm_num at hh
  have hdir : NormedSpace.normalize (a false) ≠ NormedSpace.normalize (a true) :=
    P.normalize_adjacent_cut_ne hP hinj t ht i hvertex
  have hsectionM : P.boundary ℝ = M.space ∩ {x | A x = 0} := by
    rw [hMK]
    exact hsection
  have hposM : (0 : E) ∈ closure (M.space ∩ {x | 0 < A x}) := by
    rw [hMK]
    exact hpos
  have hnegM : (0 : E) ∈ closure (M.space ∩ {x | A x < 0}) := by
    rw [hMK]
    exact hneg
  obtain ⟨_, hlinkzero, hlinkneg, hlinkpos⟩ :=
    M.original_cut_link_data_of_surface_accumulation hM hvertexM A P hP hinj
      hsectionM t ht i hvertex hposM hnegM
  have haM (j : Bool) : a j ∈ M.space := by
    rw [hMK]
    exact mem_space_iff.mpr ⟨s j, hs j, intrinsicInterior_subset (ha j)⟩
  obtain ⟨B, m, Q, p, ρ, hB, hBC, hQ, hQi, hQS, hcone, hp, hpne,
    hQzero, hQneg, hQpos⟩ :=
    M.exists_radial_cut_event_link hM hpure hcofaces hconn A hlinkzero hlinkneg hlinkpos
      hC hcv hzero hdisj hlocal Z hZ hrep J hJ hJC a haM haC hdir
      L hLheight σ hσne hLa
  have hpK (j : Bool) : p j ∈ K.space := by
    rw [← hMK]
    exact space_subset_of_le (show M.closedStar 0 ≤ M from fun _ ht => ht.1) (hp j).2.1
  have hpTriangle (j : Bool) :
      p j ∈ intrinsicInterior ℝ (convexHull ℝ (s j : Set E)) :=
    (K.mem_triangle_interior_of_radial_face_neighborhood hK hbound
      (hs j) (hcard j) (ha j) (hpK j) (hC.isClosed.frontier_subset (hp j).1)
      hfaceC (hp j).2.2.1.le (hp j).2.2.2).2
  have hQSK : Q.boundary ℝ = frontier C ∩ K.space := by
    rw [← hMK]
    exact hQS
  have hconeK : C ∩ K.space = convexJoin ℝ {0} (Q.boundary ℝ) := by
    rw [← hMK]
    exact hcone
  let Z0 : Finset (E →ₗ[ℝ] ℝ) := Finset.univ.image Z
  have hZ0 : C = {x | ∀ Q ∈ Z0, Q x ≤ 1} := by
    rw [hrep]
    ext x
    constructor
    · intro hx Q hQ
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hQ
      exact hx j
    · intro hx j
      exact hx (Z j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  obtain ⟨δ, H, F, hδ, hδR, hsource, hF, hFsource, hFPL, hFinj, hball,
    hheightF, hsurfaceF, hlateralF, hcutSource, hcutForward, hforward, hcore⟩ :=
    K.exists_actual_original_cut_box hK hbound s hs hcard a p ha hpTriangle
      f hfzero hR hsurface L hflast A hA hdim hLheight hfheight hd hdplane hinward
      B hB hC hcv hBC hzero Z0 hZ0 (fun j => (hp j).1) hpne Q hQ hQi hQSK
      hQzero hQneg hQpos hconeK ρ (fun j => (hp j).2.2.1)
      (fun j => (hp j).2.2.2) σ hσneg hσpos hlateral hε
  refine ⟨δ, H, F, k, hδ, hδR, hk, hsource, hF, ?_, hFPL, hFinj, hball,
    hheightF, hsurfaceF, hlateralF, hcutSource, ?_, hforward, ?_⟩
  · rw [hsource]
    exact hFsource
  · intro j x hx
    exact (hcutForward j x hx).trans (hfull j x)
  · rw [hcore, P.cutArc_eq_segments t (fun j => ⟨(ht j).1.le, (ht j).2.le⟩) i,
      hvertex, segment_symm ℝ (P.edgeCut t i) 0]
    rfl

end Geometry.SimplicialComplex
