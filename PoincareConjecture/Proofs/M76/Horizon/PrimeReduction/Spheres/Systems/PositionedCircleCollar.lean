import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalCircleCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleCaps

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_positioned_sphere_system_circle_collar
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 C3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source,
            x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    (hLC : L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))
    (hLinter : L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))
    (i : κ) {m : ℕ} (R : Polygon V3 (m + 3))
    (hR : R.HasSimplicialEdges) (hRi : Function.Injective R)
    {d : Set V3} (hd : IsFinitePLBallPair P2 d (R.boundary ℝ))
    (hdS : d ⊆ sphere (0 : V3) 1)
    (hrimage : (sS i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ)
    {O : Set X} (hO : IsOpen O) (hrO : Q.symm '' L.boundary ℝ ⊆ O) :
    ∃ (l : ℕ) (sigma : C3 → V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
        (Q.target ∩ Q.symm ⁻¹' O) ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (x : C3).1 ∈ signedTubeSheet 0) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        Q.symm (sigma x) ∈ ⋃ j, S j ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        Q.symm (sigma x) ∈ S i ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ => sigma ((0, 0), t)) '' Icc (0 : ℝ) (l + 3) = L.boundary ℝ ∧
      (∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
        sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
          ((x : C3).2 = (y : C3).2 ∨
            ((x : C3).2 = 0 ∧ (y : C3).2 = l + 3) ∨
            ((y : C3).2 = 0 ∧ (x : C3).2 = l + 3))) ∧
      ∀ j, j ≠ i → Disjoint
        (Q.symm '' (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)))) (S j) := by
  classical
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hLQ : L.boundary ℝ ⊆ Q.target :=
    hLinter.trans (intrinsicInterior_subset.trans hTQ)
  have hne (v : G.vertices) : (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))
    · rw [hinterior v hv]
      norm_num
    · rw [hexterior v hv]
      norm_num
  obtain ⟨Ug, hUg, hCUg, hGUg⟩ := G.exists_open_component_neighborhood hG hdim hne C
  have hLG : L.boundary ℝ ⊆ G.space := fun x hx =>
    (hGUg.symm.subset (hLC.subset hx)).1
  have hLS : Q.symm '' L.boundary ℝ ⊆ S i := by
    rw [← hrimage]
    rintro _ ⟨x, hx, rfl⟩
    rw [(sS i).map_eq ⟨x, hdS (hd.1 hx)⟩]
    exact ((sS i).parametrization ⟨x, hdS (hd.1 hx)⟩).property
  obtain ⟨Ui, hUi, hiUi, hUiWhole, hUiOther⟩ := exists_open_sphere_system_isolation S sS hdis i
  obtain ⟨J, hJ, hLJ, hJQ⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed L.isCompact_boundary
      Q.open_target hLQ
  obtain ⟨M, hM, hMs, hMdim, hMlocal, _⟩ :=
    exists_finite_sphere_system_chart_carrier S sS hdis Q hQ J hJ hJQ
  obtain ⟨T, fT, hT, hTs, hfTi⟩ := original_triangle_planar_coordinates K g hgi hs hs3 Q A hmap hA
  let V := (Ug ∩ interior J.space) ∩ (Q.target ∩ Q.symm ⁻¹' (O ∩ Ui))
  have hV : IsOpen V := (hUg.inter isOpen_interior).inter
    (Q.symm.isOpen_inter_preimage (hO.inter hUi))
  have hLV : L.boundary ℝ ⊆ V := by
    intro x hx
    exact ⟨⟨hCUg (hLC.subset hx), hLJ hx⟩, hLQ hx,
      hrO ⟨x, hx, rfl⟩, hiUi (hLS ⟨x, hx, rfl⟩)⟩
  have hmember (x : V3) (hx : x ∈ V) : Q.symm x ∈ ⋃ j, S j ↔ Q.symm x ∈ S i := by
    constructor
    · exact fun hxS => hUiWhole.subset ⟨hx.2.2.2, hxS⟩
    · exact fun hxS => (subset_iUnion S i) hxS
  have hmemberLocal (x : V3) (hx : x ∈ V) : Q.symm x ∈ S i ↔ x ∈ M.space :=
    (hmember x hx).symm.trans (hMlocal x (interior_subset hx.1.2))
  have hgraph (x : V3) (hxQ : x ∈ Q.target) :
      x ∈ G.space ↔ x ∈ T.space ∧ Q.symm x ∈ ⋃ j, S j := by
    constructor
    · intro hxG
      exact ⟨hTs.symm.subset (hGT hxG).1,
        (hphysicalGraph.subset ⟨x, hxG, rfl⟩).1⟩
    · rintro ⟨hxT, hxS⟩
      have hxPhys : Q.symm x ∈ g '' convexHull ℝ (s : Set E) := by
        obtain ⟨u, hu, hux⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset
          (hTs.subset hxT)
        refine ⟨u, hu, ?_⟩
        have hAu : Q (g u) = x := (hA hu).trans hux
        exact (Q.left_inv (hmap hu)).symm.trans (congrArg Q.symm hAu)
      obtain ⟨y, hyG, hyx⟩ := hphysicalGraph.symm.subset ⟨hxS, hxPhys⟩
      exact (Q.symm.injOn (hGT hyG).2 hxQ hyx) ▸ hyG
  have hIso (x : V3) (hx : x ∈ V) : x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ M.space := by
    rw [← hMlocal x (interior_subset hx.1.2), ← hgraph x hx.2.1]
    constructor
    · exact fun hxL => hLG hxL
    · exact fun hxG => hLC.symm.subset (hGUg.subset ⟨hxG, hx.1.1⟩)
  have hcharts : ∀ w ∈ L.boundary ℝ, ∀ U : Set V3, IsOpen U → w ∈ U →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ U ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, x ∈ T.space ↔ (B x).1.1 = 0 := by
    intro w hw U hU hwU
    obtain ⟨B, hwB, hBU, hBw, hB, hBi, hBS, hBT⟩ :=
      hcrossings w ⟨hLG hw, hLinter hw⟩ (U ∩ interior J.space)
        (hU.inter isOpen_interior) ⟨hwU, hLJ hw⟩
    refine ⟨B, hwB, hBU.trans inter_subset_left, hBw, hB, hBi, ?_, ?_⟩
    · intro x hx
      exact (hMlocal x (interior_subset (hBU hx).2)).symm.trans (hBS x hx)
    · simpa only [hTs] using hBT
  obtain ⟨l, sigma, hSigma, hSigmaV, hInt, hTriangle, hSphere, hAxis, hImage, hFib⟩ :=
    (sS i).exists_planar_circle_tube Q hQ T M hT fT hfTi L hL hLi R hR hRi
      hd hdS hrimage hV hLV (fun _ hx => hx.2.1) hmemberLocal hIso hcharts
  refine ⟨l, sigma, hSigma, fun x hx => ⟨(hSigmaV hx).2.1, (hSigmaV hx).2.2.1⟩,
    hInt, (by simpa only [hTs] using hTriangle), ?_, hSphere, hAxis, hImage, hFib, ?_⟩
  · intro x
    exact (hmember (sigma x) (hSigmaV x.property)).trans (hSphere x)
  · intro j hji
    apply (hUiOther j hji).mono_left
    rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact (hSigmaV hz).2.2.2

end PoincareConjecture.M76
