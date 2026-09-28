import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalCircleCaps









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

theorem exists_sphere_system_circle_caps_of_physical_crossings
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {n : ℕ} (L : Polygon V3 (n + 3)) (hLi : Function.Injective L)
    (hL : L.HasSimplicialEdges) {D : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDQ : D ⊆ Q.target)
    (hcap : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ)
    (i : κ) (hirim : Q.symm '' L.boundary ℝ ⊆ S i)
    (hcrossings : ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
        (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
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
  obtain ⟨J, hJ, hDJ, hJQ⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hD.isCompact
      Q.open_target hDQ
  obtain ⟨M, hM, hMs, hMdim, hMlocal, _⟩ :=
    exists_finite_sphere_system_chart_carrier S sS hdis Q hQ J hJ hJQ
  apply exists_sphere_system_circle_caps S sS hdis he hcover Q hQ
    J M hJ hJQ hMlocal L hLi hL hD hDJ hcap i hirim
  intro w hw O hO hwO
  obtain ⟨B, hwB, hBO, hBw, hBS, hBL⟩ :=
    hcrossings w hw (O ∩ interior J.space) (hO.inter isOpen_interior)
      ⟨hwO, hDJ (hD.1 hw)⟩
  refine ⟨B, hwB, hBO.trans inter_subset_left, hBw, ?_, hBL⟩
  intro x hx
  exact (hMlocal x (interior_subset (hBO hx).2)).symm.trans (hBS x hx)




theorem exists_positioned_sphere_system_circle_caps
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hNK : N ≤ K)
    (g : E → X) (hgi : InjOn g K.space)
    {Z : Set X} (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
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
      (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
      Q.symm '' L.boundary ℝ ⊆ S i ∧
      (∀ j, Q.symm '' L.boundary ℝ ⊆ S j → j = i) ∧
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
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hDG,
      hphyscompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique⟩ :=
    exists_positioned_sphere_system_face_circle_cap S sS hdis K N hNK g hgi
      hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ hdim hfinite
      hinterior hexterior hcircle
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hDQ : D ⊆ Q.target := (hDT.trans intrinsicInterior_subset).trans hTQ
  refine ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hDG,
    hphyscompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique, ?_⟩
  apply exists_sphere_system_circle_caps_of_physical_crossings S sS hdis he hcover
    Q hQ L hLi hL hD hDQ hcap i hirim
  intro w hw O hO hwO
  have hwD := hD.1 hw
  have hwG := (hDG.symm.subset hw).2
  obtain ⟨B, hwB, hBO, hBw, hB, hBinv, hBS, hBT⟩ :=
    hcrossings w ⟨hwG, hDT hwD⟩ O hO hwO
  refine ⟨B, hwB, hBO, hBw, hBS, ?_⟩
  intro x hx
  exact (hBT x hx.2).mp (intrinsicInterior_subset (hDT (hD.1 hx.1)))


end PoincareConjecture.M76
