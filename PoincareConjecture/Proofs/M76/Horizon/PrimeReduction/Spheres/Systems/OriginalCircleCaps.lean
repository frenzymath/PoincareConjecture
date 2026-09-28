import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.InnermostCircleDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.AmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)



theorem exists_sphere_system_circle_caps
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J M : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hMlocal : ∀ x ∈ J.space, Q.symm x ∈ ⋃ i, S i ↔ x ∈ M.space)
    {n : ℕ} (L : Polygon V3 (n + 3)) (hLi : Function.Injective L)
    (hL : L.HasSimplicialEdges) {D : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDJ : D ⊆ interior J.space)
    (hcap : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ)
    (i : κ) (hirim : Q.symm '' L.boundary ℝ ⊆ S i)
    (hcrossings : ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
        ∀ x ∈ L.boundary ℝ ∩ B.source, (B x).1.1 = 0) :
    ∃ (m : ℕ) (R : Polygon V3 (m + 3)) (d₀ d₁ : Set V3),
      Function.Injective R ∧ R.HasSimplicialEdges ∧
      IsFinitePLBallPair P2 d₀ (R.boundary ℝ) ∧
      IsFinitePLBallPair P2 d₁ (R.boundary ℝ) ∧
      d₀ ∪ d₁ = sphere (0 : V3) 1 ∧ d₀ ∩ d₁ = R.boundary ℝ ∧
      ((sS i).map '' d₀) ∪ ((sS i).map '' d₁) = S i ∧
      ((sS i).map '' d₀) ∩ ((sS i).map '' d₁) = Q.symm '' L.boundary ℝ ∧
      ∃ (s₀ : ChartwisePLSphere e (((sS i).map '' d₀) ∪ (Q.symm '' D)))
        (s₁ : ChartwisePLSphere e (((sS i).map '' d₁) ∪ (Q.symm '' D))),
        EqOn s₀.map (sS i).map d₀ ∧ EqOn s₁.map (sS i).map d₁ ∧
        s₀.map '' d₁ = Q.symm '' D ∧ s₁.map '' d₀ = Q.symm '' D ∧
        ((((sS i).map '' d₀) ∪ (Q.symm '' D)) ∪
          (((sS i).map '' d₁) ∪ (Q.symm '' D)) = S i ∪ (Q.symm '' D)) ∧
        ((((sS i).map '' d₀) ∪ (Q.symm '' D)) ∩
          (((sS i).map '' d₁) ∪ (Q.symm '' D)) = Q.symm '' D) ∧
        ∀ j, j ≠ i →
          Disjoint (((sS i).map '' d₀) ∪ (Q.symm '' D)) (S j) ∧
          Disjoint (((sS i).map '' d₁) ∪ (Q.symm '' D)) (S j) := by
  classical
  obtain ⟨P, hP, hPs, _, hPlocal⟩ := (sS i).exists_finite_chart_carrier Q hQ J hJ hJQ
  have hDQ : D ⊆ Q.target := hDJ.trans (interior_subset.trans hJQ)
  have hLP : L.boundary ℝ ⊆ P.space := by
    intro x hx
    exact (hPlocal x (interior_subset (hDJ (hD.1 hx)))).mp
      (hirim (mem_image_of_mem Q.symm hx))
  obtain ⟨U, hU, hiU, hUwhole, _⟩ := exists_open_sphere_system_isolation S sS hdis i
  let w := L 0
  have hw : w ∈ L.boundary ℝ := L.vertex_mem_boundary 0
  let O := interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' U)
  have hO : IsOpen O := isOpen_interior.inter (Q.symm.isOpen_inter_preimage hU)
  have hwO : w ∈ O := ⟨hDJ (hD.1 hw), hDQ (hD.1 hw),
    hiU (hirim (mem_image_of_mem Q.symm hw))⟩
  obtain ⟨B, hwB, hBO, hBw, hBM, hBL⟩ := hcrossings w hw O hO hwO
  have hBP : ∀ x ∈ B.source, x ∈ P.space ↔ (B x).2 = 0 := by
    intro x hx
    have hxO := hBO hx
    have hxJ := interior_subset hxO.1
    rw [← hPlocal x hxJ, ← hBM x hx, ← hMlocal x hxJ]
    constructor
    · exact fun hx => mem_iUnion.mpr ⟨i, hx⟩
    · intro hxS
      exact hUwhole.subset ⟨hxO.2.2, hxS⟩
  have hcapmember : (Q.symm '' D) ∩ S i = Q.symm '' L.boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcap.subset ⟨hx.1, mem_iUnion.mpr ⟨i, hx.2⟩⟩
    · exact fun x hx => ⟨image_mono hD.1 hx, hirim hx⟩
  obtain ⟨f, m, R, d₀, d₁, hf, hfi, hRi, hR, hRb, hd₀, hd₁,
      hunion, hinter, hphysical, hphysicalrim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
      hrawinter⟩ :=
    (sS i).exists_circle_caps he Q hQ (fun x _ => hcover x) J P hJ hJQ hP hPs
      L hL hLi hLP B hwB hBw hBP hBL hD hDQ hcapmember
  have hrawunion : (((sS i).map '' d₀) ∪ (Q.symm '' D)) ∪
      (((sS i).map '' d₁) ∪ (Q.symm '' D)) = S i ∪ (Q.symm '' D) := by
    calc
      _ = (((sS i).map '' d₀) ∪ ((sS i).map '' d₁)) ∪ (Q.symm '' D) := by
        ext x
        simp only [mem_union]
        tauto
      _ = _ := congrArg (fun U => U ∪ (Q.symm '' D)) hphysical
  refine ⟨m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hunion, hinter, hphysical,
    hphysicalrim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap, hrawunion, hrawinter, ?_⟩
  intro j hji
  have hDC : Disjoint (Q.symm '' D) (S j) := by
    apply disjoint_left.mpr
    intro x hxD hxj
    exact disjoint_left.mp (hdis (Ne.symm hji))
      (hirim (hcap.subset ⟨hxD, mem_iUnion.mpr ⟨j, hxj⟩⟩)) hxj
  have hdisj : Disjoint (S i ∪ (Q.symm '' D)) (S j) :=
    (hdis (Ne.symm hji)).union_left hDC
  exact ⟨hdisj.mono_left (subset_union_left.trans hrawunion.subset),
    hdisj.mono_left (subset_union_right.trans hrawunion.subset)⟩



theorem exists_original_sphere_system_circle_caps
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
              Disjoint (T₀ ∩ E₁) (T₁ ∩ E₁) ∧ Disjoint T₀ Z ∧ Disjoint T₁ Z) := by
  classical
  obtain ⟨J, M, G, Phi, W, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
      hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
      hinterior, hexterior, hfinite, hcaps⟩ :=
    exists_original_sphere_system_innermost_circle_disk S sS hdisjoint he
      K N hK hNK g hgc hgi hZ hmark hSZ hSV hs hs3 hedges hcofaces Q hQ A hmap hA hε
  obtain ⟨hsPhi, hPhiDis, hPhiSZ, _⟩ :=
    protected_sphere_system_ambient_image S sS hdisjoint hcover Phi hPhiPL hSZ
      (hfixW.mono hZW)
  let sPhi : ∀ i, ChartwisePLSphere e (Phi '' S i) := fun i => Classical.choice (hsPhi i)
  refine ⟨J, M, G, Phi, W, sPhi, hJ, hJQ, htriJ, hM, hG, hGs, hdim,
    hPhiPL, hPhiinv, hPhiS, hW, hZW, hedgeW, hfixW, hcofaces', hdisjoint',
    hinterior, hexterior, hfinite, ?_⟩
  intro hcircle
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact, hphysicalcompact,
      hphysub, hDZ, hDsk, hcap, hirim, hiunique, hcrossings⟩ := hcaps hcircle
  have hMlocal : ∀ x ∈ J.space, Q.symm x ∈ ⋃ i, Phi '' S i ↔ x ∈ M.space := by
    simpa only [image_iUnion] using hPhiS
  have hcap' : (Q.symm '' D) ∩ (⋃ i, Phi '' S i) = Q.symm '' L.boundary ℝ := by
    simpa only [image_iUnion] using hcap
  have hcrossings' : ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        (∀ x ∈ B.source, x ∈ M.space ↔ (B x).2 = 0) ∧
        ∀ x ∈ L.boundary ℝ ∩ B.source, (B x).1.1 = 0 := by
    intro w hw O hO hwO
    obtain ⟨B, hwB, hBO, hBw, hBPL, hBinv, hBM, hBT⟩ := hcrossings w hw O hO hwO
    refine ⟨B, hwB, hBO, hBw, hBM, ?_⟩
    intro x hx
    exact (hBT x hx.2).mp (intrinsicInterior_subset (hDT (hD.1 hx.1)))
  obtain ⟨m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
      hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
      hrawunion, hrawinter, hother⟩ :=
    exists_sphere_system_circle_caps (fun i => Phi '' S i) sPhi hPhiDis he hcover Q hQ
      J M hJ hJQ hMlocal L hLi hL hD
      (fun x hx => htriJ (intrinsicInterior_subset (hDT hx))) hcap' i hirim hcrossings'
  refine ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hexact,
    hphysicalcompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique, hcrossings,
    m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
    hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
    hrawunion, hrawinter, hother, ?_⟩
  let E₁ : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
    g '' convexHull ℝ (a : Set E)
  let T₀ := ((sPhi i).map '' d₀) ∪ (Q.symm '' D)
  let T₁ := ((sPhi i).map '' d₁) ∪ (Q.symm '' D)
  change (T₀ ∪ T₁) ∩ E₁ = S i ∩ E₁ ∧
    Disjoint (T₀ ∩ E₁) (T₁ ∩ E₁) ∧ Disjoint T₀ Z ∧ Disjoint T₁ Z
  have hEfix : EqOn Phi id E₁ := by
    intro x hx
    obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨ha2, hxa⟩ := mem_iUnion.mp hx
    exact hfixW (hedgeW a ha ha2 hxa)
  have hPhiContact : (Phi '' S i) ∩ E₁ = S i ∩ E₁ := by
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy, hyx⟩, hxE⟩
      have hfix : Phi x = x := hEfix hxE
      have hyx' : y = x := Phi.injective (hyx.trans hfix.symm)
      exact ⟨hyx' ▸ hy, hxE⟩
    · rintro x ⟨hxS, hxE⟩
      exact ⟨⟨x, hxS, hEfix hxE⟩, hxE⟩
  have hrawZ : Disjoint (T₀ ∪ T₁) Z := by
    rw [hrawunion]
    exact (hPhiSZ.mono_left (subset_iUnion (fun j => Phi '' S j) i)).union_left hDZ
  refine ⟨?_, ?_, hrawZ.mono_left subset_union_left, hrawZ.mono_left subset_union_right⟩
  · rw [hrawunion, union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hDsk,
      union_empty, hPhiContact]
  · apply disjoint_left.mpr
    intro x hx₀ hx₁
    exact disjoint_left.mp hDsk (hrawinter.subset ⟨hx₀.1, hx₁.1⟩) hx₀.2

end PoincareConjecture.M76
