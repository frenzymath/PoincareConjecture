import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleSphereScene
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRetainedCircleDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ComponentNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.AffineFaceCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalTrianglePlane

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem original_triangle_planar_coordinates
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ (T : SimplicialComplex ℝ V3) (f : V3 →ᴬ[ℝ] V2),
      T.faces.Finite ∧ T.space = convexHull ℝ (A '' (s : Set E)) ∧ InjOn f T.space := by
  obtain ⟨F, R, hRF, hFR⟩ := original_triangle_plane_coordinates K g hgi hs hs3 Q A hmap hA
  obtain ⟨T, hT, hTs⟩ := K.exists_finite_affine_face_carrier hs A
  let E₂ := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let f : V3 →ᴬ[ℝ] V2 := E₂.toContinuousAffineEquiv.toContinuousAffineMap.comp R
  refine ⟨T, f, hT, hTs, ?_⟩
  intro x hx y hy hxy
  have hxspan := convexHull_subset_affineSpan (A '' (s : Set E)) (hTs.subset hx)
  have hyspan := convexHull_subset_affineSpan (A '' (s : Set E)) (hTs.subset hy)
  exact (hFR hxspan).symm.trans ((congrArg F (E₂.injective hxy)).trans (hFR hyspan))

theorem exists_original_sphere_system_circle_collar
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (J M G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) (W : Set X)
      (sPhi : ∀ i, ChartwisePLSphere e (Phi '' S i)),
      J.faces.Finite ∧ J.space ⊆ Q.target ∧
      convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space ∧
      M.faces.Finite ∧ G.faces.Finite ∧
      G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)) ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space) ∧
      IsOpen W ∧ Z ⊆ W ∧
      (∀ a ∈ K.faces, a.card ≤ 2 → g '' convexHull ℝ (a : Set E) ⊆ W) ∧
      EqOn Phi id W ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      (∀ v : G.vertices,
        (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : G.vertices,
        (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
          (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      ((∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
          intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) →
      ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
        (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3) (i : κ),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧ IsCompact D ∧
        D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
        D ∩ G.space = L.boundary ℝ ∧
        (Q.symm '' D) ∩ Phi '' (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
        Q.symm '' L.boundary ℝ ⊆ Phi '' S i ∧
        ∃ (m : ℕ) (R : Polygon V3 (m + 3)) (d₀ d₁ : Set V3),
          Function.Injective R ∧ R.HasSimplicialEdges ∧
          IsFinitePLBallPair P2 d₀ (R.boundary ℝ) ∧
          IsFinitePLBallPair P2 d₁ (R.boundary ℝ) ∧
          d₀ ∪ d₁ = sphere (0 : V3) 1 ∧ d₀ ∩ d₁ = R.boundary ℝ ∧
          (sPhi i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ ∧
          ∃ (s₀ : ChartwisePLSphere e (((sPhi i).map '' d₀) ∪ (Q.symm '' D)))
            (s₁ : ChartwisePLSphere e (((sPhi i).map '' d₁) ∪ (Q.symm '' D))),
            EqOn s₀.map (sPhi i).map d₀ ∧ EqOn s₁.map (sPhi i).map d₁ ∧
            s₀.map '' d₁ = Q.symm '' D ∧ s₁.map '' d₀ = Q.symm '' D ∧
            ((((sPhi i).map '' d₀) ∪ (Q.symm '' D)) ∩
              (((sPhi i).map '' d₁) ∪ (Q.symm '' D)) = Q.symm '' D) ∧
            let E₁ : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
              g '' convexHull ℝ (a : Set E)
            ∃ O : Set X, IsOpen O ∧ Q.symm '' D ⊆ O ∧ O ⊆ Q.source ∧
              Disjoint O Z ∧ Disjoint O E₁ ∧
              (∀ j, j ≠ i → Disjoint O (Phi '' S j)) ∧
              let d : Fin 2 → Set V3 := ![d₀, d₁]
              ∃ (a : Fin 2 → ℝ) (f : Fin 2 → P2 → V3) (k q b : Fin 2 → Set V3),
                (∀ j, 0 < a j ∧ a j < 1 ∧
                  FinitePiecewiseAffineOn (f j) (closedBall (0 : P2) 1) ∧
                  InjOn (f j) (closedBall (0 : P2) 1) ∧
                  f j '' closedBall (0 : P2) 1 = d j ∧
                  f j '' sphere (0 : P2) 1 = R.boundary ℝ ∧
                  k j = f j '' closedBall (0 : P2) (a j) ∧
                  q j = f j '' sphere (0 : P2) (a j) ∧
                  b j = f j '' {x : P2 | ‖x‖ ∈ Icc (a j) 1} ∧
                  IsFinitePLBallPair P2 (k j) (q j) ∧
                  k j ∪ b j = d j ∧ k j ∩ b j = q j ∧
                  Disjoint (k j) (R.boundary ℝ) ∧ R.boundary ℝ ⊆ b j ∧
                  (sPhi i).map '' b j ⊆ O ∧
                  PolyhedralPLInCharts e (sPhi i).map (k j) ∧
                  PolyhedralPLInCharts e (sPhi i).map (b j) ∧
                  PolyhedralPLInCharts e ((sPhi i).map ∘ f j) (closedBall (0 : P2) 1) ∧
                  ∃ H : {x : P2 | ‖x‖ ∈ Icc (a j) 1} ≃ₜ b j,
                    H.IsFinitePL ∧ ∀ x, (H x : V3) = f j x) ∧
                Disjoint ((sPhi i).map '' k 0) ((sPhi i).map '' k 1) ∧
                ((sPhi i).map '' b 0) ∩ ((sPhi i).map '' b 1) =
                  (sPhi i).map '' R.boundary ℝ ∧
                EqOn s₀.map (sPhi i).map (k 0) ∧ EqOn s₁.map (sPhi i).map (k 1) ∧
                ∀ V : Set V3, IsOpen V → L.boundary ℝ ⊆ V →
                ∃ (l : ℕ) (sigma : C3 → V3),
                  FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) ∧
                  MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
                    (V ∩ (Q.target ∩ Q.symm ⁻¹' O)) ∧
                  L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))) ∧
                  (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
                    sigma x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (x : C3).1 ∈ signedTubeSheet 0) ∧
                  (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
                    Q.symm (sigma x) ∈ Phi '' (⋃ j, S j) ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
                  (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
                    Q.symm (sigma x) ∈ Phi '' S i ↔ (x : C3).1 ∈ signedTubeSheet 1) ∧
                  (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
                    sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
                  (fun t : ℝ => sigma ((0, 0), t)) '' Icc (0 : ℝ) (l + 3) = L.boundary ℝ ∧
                  ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)),
                    sigma x = sigma y ↔ (x : C3).1 = (y : C3).1 ∧
                      ((x : C3).2 = (y : C3).2 ∨
                        ((x : C3).2 = 0 ∧ (y : C3).2 = l + 3) ∨
                        ((y : C3).2 = 0 ∧ (x : C3).2 = l + 3))) := by
  classical
  obtain ⟨J, M, G, Phi, W, sPhi, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
      hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
      hinterior, hexterior, hfinite, hcaps⟩ :=
    exists_original_sphere_system_retained_circle_disks S sS hdisjoint he hcover
      K N hK hNK g hgc hgi hZ hmark hSZ hSV hs hs3 hedges hcofaces Q hQ A hmap hA hε
  refine ⟨J, M, G, Phi, W, sPhi, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
    hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
    hinterior, hexterior, hfinite, ?_⟩
  intro hcircle
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact,
      hphysicalcompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique, hcrossings,
      m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
      hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
      hrawunion, hrawinter, hother, hcontacts, hcontactdis, hraw₀Z, hraw₁Z,
      O, hO, hDO, hOQ, hOZ, hOE, hOj,
      a, f, k, q, b, hside, hkk, hbb, hpkk, hpbb, hphysical, hsk₀, hsk₁⟩ := hcaps hcircle
  have hdS (j : Fin 2) : (![d₀, d₁] j) ⊆ sphere (0 : V3) 1 := by
    fin_cases j
    · exact subset_union_left.trans hparamunion.subset
    · exact subset_union_right.trans hparamunion.subset
  have hsi : InjOn (sPhi i).map (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    rw [(sPhi i).map_eq ⟨x, hx⟩, (sPhi i).map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val ((sPhi i).parametrization.injective (Subtype.ext hxy))
  have hrimage : (sPhi i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ := by
    rw [← hparaminter, image_inter_on (s := d₀) (t := d₁)
      (fun x hx y hy hxy => hsi (hdS 1 hx) (hdS 0 hy) hxy)]
    exact hpiecerim
  refine ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact, hcap, hirim,
    m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter, hrimage,
    s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap, hrawinter,
    O, hO, hDO, hOQ, hOZ, hOE, hOj, a, f, k, q, b, hside,
    hpkk, hpbb, hsk₀, hsk₁, ?_⟩
  intro V hV hLV
  have hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
    letI : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
    intro v
    apply (Set.ncard_pos (Set.toFinite _)).mp
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))
    · rw [hinterior v hv]
      norm_num
    · rw [hexterior v hv]
      norm_num
  obtain ⟨Ug, hUg, hCUg, hGUg⟩ := G.exists_open_component_neighborhood hG hdim hne C
  obtain ⟨T, fT, hT, hTs, hfTi⟩ := original_triangle_planar_coordinates K g hgi hs hs3 Q A hmap hA
  let Oc := (Ug ∩ interior J.space) ∩ (V ∩ (Q.target ∩ Q.symm ⁻¹' O))
  have hOc : IsOpen Oc := (hUg.inter isOpen_interior).inter
    (hV.inter (Q.symm.isOpen_inter_preimage hO))
  have hLOc : L.boundary ℝ ⊆ Oc := by
    intro x hx
    have hxD := hD.1 hx
    have hxJ := htriJ (intrinsicInterior_subset (hDT hxD))
    exact ⟨⟨hCUg (hLC.subset hx), hxJ⟩, hLV hx, hJQ (interior_subset hxJ),
      hDO ⟨x, hxD, rfl⟩⟩
  have hmember (x : V3) (hx : x ∈ Oc) :
      Q.symm x ∈ Phi '' (⋃ j, S j) ↔ Q.symm x ∈ Phi '' S i := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · exact ⟨y, hji ▸ hj, hyx⟩
      · exact (disjoint_left.mp (hOj j hji) hx.2.2.2 ⟨y, hj, hyx⟩).elim
    · exact fun hxS => image_mono (f := Phi) (subset_iUnion S i) hxS
  have hMlocal (x : V3) (hx : x ∈ Oc) : Q.symm x ∈ Phi '' S i ↔ x ∈ M.space :=
    (hmember x hx).symm.trans (hPhiS x (interior_subset hx.1.2))
  have hIso (x : V3) (hx : x ∈ Oc) :
      x ∈ L.boundary ℝ ↔ x ∈ T.space ∧ x ∈ M.space := by
    rw [hTs]
    constructor
    · intro hxL
      have hxG := (hGUg.symm.subset (hLC.subset hxL)).1
      exact (hGs.subset hxG).symm
    · intro hxt
      exact hLC.symm.subset (hGUg.subset ⟨hGs.symm.subset hxt.symm, hx.1.1⟩)
  obtain ⟨l, sigma, hSigma, hSigmaO, hInt, htriangle, hsphere, haxis, himage, hfib⟩ :=
    (sPhi i).exists_planar_circle_tube Q hQ T M hT fT hfTi L hL hLi R hR hRi
      hd₀ (hdS 0) hrimage hOc hLOc (fun _ hx => hx.2.2.1) hMlocal hIso
      (by simpa only [hTs] using hcrossings)
  refine ⟨l, sigma, hSigma, fun x hx => (hSigmaO hx).2, hInt,
    (by simpa only [hTs] using htriangle), ?_, hsphere, haxis, himage, hfib⟩
  intro x
  exact (hmember (sigma x) (hSigmaO x.property)).trans (hsphere x)

end PoincareConjecture.M76
