import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalCircleCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SeparatedCircleCapsRetainedDisks










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)




theorem exists_original_sphere_system_retained_circle_disks
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
        IsCompact (Q.symm '' D) ∧
        Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
        Disjoint (Q.symm '' D) Z ∧
        Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
          g '' convexHull ℝ (a : Set E)) ∧
        (Q.symm '' D) ∩ Phi '' (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
        Q.symm '' L.boundary ℝ ⊆ Phi '' S i ∧
        (∀ j, Q.symm '' L.boundary ℝ ⊆ Phi '' S j → j = i) ∧
        (∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 (P2 × ℝ),
            w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source,
              x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
        ∃ (m : ℕ) (R : Polygon V3 (m + 3)) (d₀ d₁ : Set V3),
          Function.Injective R ∧ R.HasSimplicialEdges ∧
          IsFinitePLBallPair P2 d₀ (R.boundary ℝ) ∧
          IsFinitePLBallPair P2 d₁ (R.boundary ℝ) ∧
          d₀ ∪ d₁ = sphere (0 : V3) 1 ∧ d₀ ∩ d₁ = R.boundary ℝ ∧
          ((sPhi i).map '' d₀) ∪ ((sPhi i).map '' d₁) = Phi '' S i ∧
          ((sPhi i).map '' d₀) ∩ ((sPhi i).map '' d₁) = Q.symm '' L.boundary ℝ ∧
          ∃ (s₀ : ChartwisePLSphere e (((sPhi i).map '' d₀) ∪ (Q.symm '' D)))
            (s₁ : ChartwisePLSphere e (((sPhi i).map '' d₁) ∪ (Q.symm '' D))),
            EqOn s₀.map (sPhi i).map d₀ ∧ EqOn s₁.map (sPhi i).map d₁ ∧
            s₀.map '' d₁ = Q.symm '' D ∧ s₁.map '' d₀ = Q.symm '' D ∧
            ((((sPhi i).map '' d₀) ∪ (Q.symm '' D)) ∪
              (((sPhi i).map '' d₁) ∪ (Q.symm '' D)) = (Phi '' S i) ∪ (Q.symm '' D)) ∧
            ((((sPhi i).map '' d₀) ∪ (Q.symm '' D)) ∩
              (((sPhi i).map '' d₁) ∪ (Q.symm '' D)) = Q.symm '' D) ∧
            (∀ j, j ≠ i →
              Disjoint (((sPhi i).map '' d₀) ∪ (Q.symm '' D)) (Phi '' S j) ∧
              Disjoint (((sPhi i).map '' d₁) ∪ (Q.symm '' D)) (Phi '' S j)) ∧
            let E₁ : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
              g '' convexHull ℝ (a : Set E)
            let T₀ := ((sPhi i).map '' d₀) ∪ (Q.symm '' D)
            let T₁ := ((sPhi i).map '' d₁) ∪ (Q.symm '' D)
            (T₀ ∪ T₁) ∩ E₁ = S i ∩ E₁ ∧
              Disjoint (T₀ ∩ E₁) (T₁ ∩ E₁) ∧ Disjoint T₀ Z ∧ Disjoint T₁ Z ∧
              ∃ O : Set X, IsOpen O ∧ Q.symm '' D ⊆ O ∧ O ⊆ Q.source ∧
                Disjoint O Z ∧ Disjoint O E₁ ∧
                (∀ j, j ≠ i → Disjoint O (Phi '' S j)) ∧
                let d : Fin 2 → Set V3 := ![d₀, d₁]
                ∃ (a : Fin 2 → ℝ) (f : Fin 2 → P2 → V3)
                      (k q b : Fin 2 → Set V3),
                      (∀ j, 0 < a j ∧ a j < 1 ∧
                        FinitePiecewiseAffineOn (f j) (closedBall (0 : P2) 1) ∧
                        InjOn (f j) (closedBall (0 : P2) 1) ∧
                        f j '' closedBall (0 : P2) 1 = d j ∧
                        f j '' sphere (0 : P2) 1 = (R.boundary ℝ) ∧
                        k j = f j '' closedBall (0 : P2) (a j) ∧
                        q j = f j '' sphere (0 : P2) (a j) ∧
                        b j = f j '' {x : P2 | ‖x‖ ∈ Icc (a j) 1} ∧
                        IsFinitePLBallPair P2 (k j) (q j) ∧
                        k j ∪ b j = d j ∧ k j ∩ b j = q j ∧
                        Disjoint (k j) (R.boundary ℝ) ∧ (R.boundary ℝ) ⊆ b j ∧
                        (sPhi i).map '' b j ⊆ O ∧
                        PolyhedralPLInCharts e (sPhi i).map (k j) ∧
                        PolyhedralPLInCharts e (sPhi i).map (b j) ∧
                        PolyhedralPLInCharts e ((sPhi i).map ∘ f j) (closedBall (0 : P2) 1) ∧
                        ∃ H : {x : P2 | ‖x‖ ∈ Icc (a j) 1} ≃ₜ b j,
                          H.IsFinitePL ∧ (∀ x, (H x : V3) = f j x)) ∧
                      Disjoint (k 0) (k 1) ∧ b 0 ∩ b 1 = (R.boundary ℝ) ∧
                      Disjoint ((sPhi i).map '' k 0) ((sPhi i).map '' k 1) ∧
                      ((sPhi i).map '' b 0) ∩ ((sPhi i).map '' b 1) = (sPhi i).map '' (R.boundary ℝ) ∧
                      ((sPhi i).map '' k 0) ∪ ((sPhi i).map '' b 0) ∪
                        (((sPhi i).map '' k 1) ∪ ((sPhi i).map '' b 1)) = (Phi '' S i) ∧
                  EqOn s₀.map (sPhi i).map (k 0) ∧
                  EqOn s₁.map (sPhi i).map (k 1)) := by
  classical
  obtain ⟨J, M, G, Phi, W, sPhi, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
      hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
      hinterior, hexterior, hfinite, hcaps⟩ :=
    exists_original_sphere_system_circle_caps S sS hdisjoint he hcover
      K N hK hNK g hgc hgi hZ hmark hSZ hSV hs hs3 hedges hcofaces Q hQ A hmap hA hε
  refine ⟨J, M, G, Phi, W, sPhi, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
    hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
    hinterior, hexterior, hfinite, ?_⟩
  intro hcircle
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact,
      hphysicalcompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique, hcrossings,
      m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
      hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
      hrawunion, hrawinter, hother, hcontacts⟩ := hcaps hcircle
  refine ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact,
    hphysicalcompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique, hcrossings,
    m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
    hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
    hrawunion, hrawinter, hother, hcontacts.1, hcontacts.2.1,
    hcontacts.2.2.1, hcontacts.2.2.2, ?_⟩
  let E₁ : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
    g '' convexHull ℝ (a : Set E)
  have hE₁ : IsClosed E₁ := hK.isClosed_biUnion fun a ha => isClosed_iUnion_of_finite
    fun _ => ((a.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hgc.mono (K.convexHull_subset_space ha))).isClosed
  let others : Set X := ⋃ j : {j : κ // j ≠ i}, Phi '' S j.val
  have hothers : IsClosed others :=
    isClosed_iUnion_of_finite fun j : {j : κ // j ≠ i} => (sPhi j.val).isCompact.isClosed
  let O := Q.source ∩ (Z ∪ E₁ ∪ others)ᶜ
  have hO : IsOpen O := Q.open_source.inter ((hZ.union hE₁).union hothers).isOpen_compl
  have hDO : Q.symm '' D ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ := hJQ (interior_subset (htriJ (intrinsicInterior_subset (hDT hx))))
    refine ⟨Q.map_target hxQ, ?_⟩
    rintro (hZsk | hoth)
    · rcases hZsk with hz | hsk
      · exact disjoint_left.mp hDZ ⟨x, hx, rfl⟩ hz
      · exact disjoint_left.mp hDsk ⟨x, hx, rfl⟩ hsk
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hoth
      exact disjoint_left.mp (hother j.val j.property).1
        (Or.inr ⟨x, hx, rfl⟩) hj
  have hOZ : Disjoint O Z := by
    exact disjoint_left.mpr (fun x hx hz => hx.2 (Or.inl (Or.inl hz)))
  have hOE : Disjoint O E₁ := by
    exact disjoint_left.mpr (fun x hx he => hx.2 (Or.inl (Or.inr he)))
  have hOj (j : κ) (hji : j ≠ i) : Disjoint O (Phi '' S j) := by
    apply disjoint_left.mpr
    intro x hx hj
    exact hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))
  refine ⟨O, hO, hDO, inter_subset_left, hOZ, hOE, hOj, ?_⟩
  let d : Fin 2 → Set V3 := ![d₀, d₁]
  have hd (j : Fin 2) : IsFinitePLBallPair P2 (d j) (R.boundary ℝ) := by
    fin_cases j
    · exact hd₀
    · exact hd₁
  have hdS (j : Fin 2) : d j ⊆ sphere (0 : V3) 1 := by
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
  have hrO : (sPhi i).map '' R.boundary ℝ ⊆ O := by
    rw [hrimage]
    exact (image_mono hD.1).trans hDO
  obtain ⟨a, f, k, q, b, hside, hkk, hbb, hpkk, hpbb, hphysical⟩ :=
    (sPhi i).exists_separated_retained_circle_disks d hd hparamunion hparaminter hO hrO
  refine ⟨a, f, k, q, b, hside, hkk, hbb, hpkk, hpbb, hphysical, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hkb, _⟩ := hside 0
    exact hs₀.mono (subset_union_left.trans hkb.subset)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hkb, _⟩ := hside 1
    exact hs₁.mono (subset_union_left.trans hkb.subset)

end PoincareConjecture.M76
