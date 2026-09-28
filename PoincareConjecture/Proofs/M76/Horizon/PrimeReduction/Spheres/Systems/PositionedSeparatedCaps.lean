import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NormalCircleCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.SeparatedTubeCaps









set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex
namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_positioned_sphere_system_separated_caps
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
    {O : Set X} (hO : IsOpen O) (hrO : Q.symm '' L.boundary ℝ ⊆ O)
    {D : Set V3} (hD : IsFinitePLBallPair P2 D (L.boundary ℝ))
    (hDT : D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))))
    (hDfamily : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ)
    (hDO : Q.symm '' D ⊆ O) :
    ∃ (H : V3 →ᴬ[ℝ] ℝ) (l : ℕ) (sigma : C3 → V3),
      H.linear ≠ 0 ∧
      (∀ x, H x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E))) ∧
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
      (∀ j, j ≠ i → Disjoint
        (Q.symm '' (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)))) (S j)) ∧
      (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
        H (sigma x) = 0 ↔ x.1.1 = 0) ∧
      (((∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          0 < x.1.1 → 0 < H (sigma x)) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          x.1.1 < 0 → H (sigma x) < 0)) ∨
       ((∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          0 < x.1.1 → H (sigma x) < 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
          x.1.1 < 0 → 0 < H (sigma x)))) ∧
      ∃ caps : Bool → Set V3,
        (∀ b, IsFinitePLBallPair P2 (caps b)
          ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc 0 (l + 3)) ∧
          caps b ⊆ Q.target ∧ Q.symm '' caps b ⊆ O ∧
          (Q.symm '' caps b) ∩ (⋃ j, S j) =
            Q.symm '' ((fun t => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) ''
              Icc 0 (l + 3)) ∧
          Disjoint (caps b) (convexHull ℝ (A '' (s : Set E)))) ∧
        Disjoint (caps true) (caps false) ∧
        Disjoint (Q.symm '' caps true) (Q.symm '' caps false) := by
  classical
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hDQ : D ⊆ Q.target := hDT.trans (intrinsicInterior_subset.trans hTQ)
  have hLQ := hD.1.trans hDQ
  obtain ⟨J, hJ, hDJ, hJQ⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hD.isCompact
      Q.open_target hDQ
  obtain ⟨M, hM, hMs, hMdim, hMlocal, _⟩ :=
    exists_finite_sphere_system_chart_carrier S sS hdis Q hQ J hJ hJQ
  let O' := O ∩ (Q.source ∩ Q ⁻¹' interior J.space)
  have hO' : IsOpen O' := hO.inter (Q.isOpen_inter_preimage isOpen_interior)
  have hDO' : Q.symm '' D ⊆ O' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hDO ⟨x, hx, rfl⟩, Q.map_target (hDQ hx), ?_⟩
    change Q (Q.symm x) ∈ interior J.space
    rw [Q.right_inv (hDQ hx)]
    exact hDJ hx
  obtain ⟨H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
      hMember, hAxis, hImage, hFib, hOther, hzero, hsides⟩ :=
    exists_positioned_sphere_system_normal_circle_collar S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi hd hdS hrimage hO' (image_mono hD.1 |>.trans hDO')
  have hSigmaJ : MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) J.space := by
    intro x hx
    have h := (hMap hx).2.2.2
    change Q (Q.symm (sigma x)) ∈ interior J.space at h
    rw [Q.right_inv (hMap hx).1] at h
    exact interior_subset h
  have hDM : D ∩ M.space = L.boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxM⟩
      have hp := hDfamily.subset
        ⟨⟨x, hxD, rfl⟩, (hMlocal x (interior_subset (hDJ hxD))).mpr hxM⟩
      obtain ⟨y, hy, heq⟩ := hp
      exact (Q.symm.injOn (hLQ hy) (hDQ hxD) heq) ▸ hy
    · intro x hx
      refine ⟨hD.1 hx, (hMlocal x (interior_subset (hDJ (hD.1 hx)))).mp ?_⟩
      exact (hDfamily.symm.subset ⟨x, hx, rfl⟩).2
  obtain ⟨F, R₀, hRF, hFR⟩ := original_triangle_plane_coordinates K g hgi hs hs3 Q A hmap hA
  let V := Q.target ∩ Q.symm ⁻¹' O'
  have hV : IsOpen V := Q.symm.isOpen_inter_preimage hO'
  have hDV : D ⊆ V := fun x hx => ⟨hDQ hx, hDO' ⟨x, hx, rfl⟩⟩
  obtain ⟨caps, hcaps, hdisCaps⟩ := exists_separated_caps_of_circle_tube L hL hLi hD
    (hDT.trans intrinsicInterior_subset) F R₀ hRF
    (hFR.mono (convexHull_subset_affineSpan _)) M hM hDM hV hDV
    (by positivity : (0 : ℝ) < l + 3) sigma hSigma hMap
    (fun x hx => hTriangle ⟨x, hx⟩)
    (fun x hx => (hMlocal (sigma x) (hSigmaJ hx)).symm.trans (hSphere ⟨x, hx⟩))
    (fun x hx => hAxis ⟨x, hx⟩)
    (fun x hx y hy => hFib ⟨x, hx⟩ ⟨y, hy⟩)
    H.toAffineMap hH (fun x hx => (hplane x).mpr (convexHull_subset_affineSpan _ hx))
    hzero hsides
  refine ⟨H, l, sigma, hH, hplane, hSigma, ?_, hInt, hTriangle, hSphere, hMember,
    hAxis, hImage, hFib, hOther, hzero, hsides, caps, ?_, hdisCaps, ?_⟩
  · exact fun x hx => ⟨(hMap hx).1, (hMap hx).2.1⟩
  · intro b
    obtain ⟨hball, hcapV, hcapM, hcapT⟩ := hcaps b
    refine ⟨hball, fun x hx => (hcapV hx).1, ?_, ?_, hcapT⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (hcapV hx).2.1
    · apply Subset.antisymm
      · rintro y ⟨⟨x, hx, rfl⟩, hxS⟩
        have hxJ : x ∈ J.space := by
          have hh := (hcapV hx).2.2.2
          change Q (Q.symm x) ∈ interior J.space at hh
          rw [Q.right_inv (hcapV hx).1] at hh
          exact interior_subset hh
        exact ⟨x, hcapM.subset ⟨hx, (hMlocal x hxJ).mp hxS⟩, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        have hxc := hball.1 hx
        have hxJ : x ∈ J.space := by
          have hh := (hcapV hxc).2.2.2
          change Q (Q.symm x) ∈ interior J.space at hh
          rw [Q.right_inv (hcapV hxc).1] at hh
          exact interior_subset hh
        exact ⟨⟨x, hxc, rfl⟩, (hMlocal x hxJ).mpr (hcapM.symm.subset hx).2⟩
  · apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hzx : z = x := Q.symm.injOn ((hcaps false).2.1 hz).1
      ((hcaps true).2.1 hx).1 heq
    exact disjoint_left.mp hdisCaps hx (hzx ▸ hz)

end PoincareConjecture.M76

