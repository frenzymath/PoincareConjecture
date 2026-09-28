import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalReturningPlanarDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialPlanarCompression











set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Rim" => sphere (0 : Fin 2 → ℝ) 1

theorem exists_original_planar_polygon_for_disk_rim
    {X α V : Type*} [MetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E) (hKB : frontier K.space = K.space ∩ B)
    (hproperK : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    {d q : Set V} (hd : IsFinitePLBallPair P2 d q) (j : V → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjE : MapsTo j d (interior E)) (hproper : ∀ z ∈ d,j z ∈ S ↔ z ∈ q) :
    ∃ n, ∃ L : Polygon P2 (n+3), L.HasSimplicialEdges ∧ Function.Injective L ∧
      L.boundary ℝ ⊆ interior K.space ∧ p '' L.boundary ℝ = j '' q := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hpe := (hp.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hh => Subtype.ext (hpi x.property y.property hh))).isEmbedding
  obtain ⟨k,hkc,hleft,hright,hkK⟩ := hpe.exists_inverse_on_image
  have hjK : j '' q ⊆ p '' K.space := by
    rw [hps]
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨(hproper z (hd.1 hz)).mpr hz,interior_subset (hjE (hd.1 hz))⟩
  obtain ⟨n,P,hPi,hP,hPb⟩ := hd.exists_polygon_boundary
  let A := P.simplicialComplex hP
  have hA := P.finite_simplicialComplex_faces hP
  have hAs : A.space = q := (P.simplicialComplex_space hP).trans hPb
  have hkj : FinitePiecewiseAffineOn (k ∘ j) q := by
    rw [←hAs]
    apply hp.finitePiecewiseAffineOn_lift he hpi A hA
      (hkc.comp (hj.continuousOn.mono (hAs.subset.trans hd.1))
        (fun z hz => hjK ⟨z,hAs.subset hz,rfl⟩))
      (fun z hz => hkK (hjK ⟨z,hAs.subset hz,rfl⟩))
    exact (hj.restrict_finite A hA (hAs.subset.trans hd.1)).congr
      (fun z hz => (hright _ (hjK ⟨z,hAs.subset hz,rfl⟩)).symm)
  have hkji : InjOn (k ∘ j) q := by
    intro z hz w hw hzw
    exact hji (hd.1 hz) (hd.1 hw) ((hright _ (hjK ⟨z,hz,rfl⟩)).symm.trans
      ((congrArg p hzw).trans (hright _ (hjK ⟨w,hw,rfl⟩))))
  obtain ⟨m,L,hLi,hL,hLb⟩ := P.exists_polygon_finitePL_image hP hPi hkj
    hPb.subset (hkji.mono hPb.subset)
  have hLeq : L.boundary ℝ = (k ∘ j) '' q := by rw [hLb,hPb]
  refine ⟨m,L,hL,hLi,?_,?_⟩
  · rw [hLeq]
    rintro _ ⟨z,hz,rfl⟩
    have hzK := hkK (hjK ⟨z,hz,rfl⟩)
    by_contra hnot
    have hfront : k (j z) ∈ frontier K.space := ⟨subset_closure hzK,hnot⟩
    have hB := (hKB.subset hfront).2
    have hF := (hproperK _ hzK).mpr hB
    rw [hright _ (hjK ⟨z,hz,rfl⟩)] at hF
    exact hF.2 (hjE (hd.1 hz))
  · rw [hLeq,←image_comp]
    exact image_congr (fun z hz => hright _ (hjK ⟨z,hz,rfl⟩))

theorem nullhomotopic_of_original_planar_polygon_filling
    {X : Type*} [MetricSpace X] {A : Set X} {K : Set P2}
    (hK : IsCompact K) (p : P2 → X) (hp : ContinuousOn p K) (hpi : InjOn p K)
    (hps : p '' K = A) {n : ℕ} (L : Polygon P2 (n+3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    (hfill : closure L.inside ⊆ K)
    (gamma : C(Rim,A)) (hrange : range (fun z => (gamma z : X)) ⊆ p '' L.boundary ℝ) :
    gamma.Nullhomotopic := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hpe := (hp.domRestrict.isClosedEmbedding
    (fun x y hh => Subtype.ext (hpi x.property y.property hh))).isEmbedding
  obtain ⟨k,hkc,hleft,hright,hkK⟩ := hpe.exists_inverse_on_image
  let D := closure L.inside
  have hD : IsFinitePLBallPair P2 D (L.boundary ℝ) := L.isFinitePLBallPair_closed_inside hL hLi
  have hg (z : Rim) : k (gamma z) ∈ D := by
    obtain ⟨x,hx,hxp⟩ := hrange (mem_range_self z)
    rw [←hxp,hleft x (hfill (hD.1 hx))]
    exact hD.1 hx
  let lift : C(Rim,D) := ⟨fun z => ⟨k (gamma z),hg z⟩,
    (hkc.comp_continuous (continuous_subtype_val.comp gamma.continuous)
      (fun z => hps.symm.subset (gamma z).property)).subtype_mk _⟩
  let out : C(D,A) := ⟨fun z => ⟨p z,hps.subset ⟨z,hfill z.property,rfl⟩⟩,
    ((hp.mono hfill).domRestrict).subtype_mk _⟩
  have hcontract : ContractibleSpace D := by
    obtain ⟨_,C,_,hcv,hne,H,_,_⟩ := hD
    let : Nonempty C := ⟨⟨hne.some,interior_subset hne.some_mem⟩⟩
    let : ContractibleSpace C := hcv.contractibleSpace (hne.mono interior_subset)
    exact H.contractibleSpace
  let := hcontract
  have heq : out.comp lift = gamma := by
    ext z
    exact hright _ (hps.symm.subset (gamma z).property)
  rw [←heq]
  exact ((id_nullhomotopic D).comp_right out).comp_left lift

local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem ChartwisePLSphere.rim_nullhomotopic_of_proper_compression_at_minimum
    {X α V : Type*} [MetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : α → OpenPartialHomeomorph X V3} {R S E D : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (heE : PLDomain e E) (hR : IsCompact R)
    (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (hE : IsClosed E) (hER : E ⊆ R)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hDQ : D ⊆ Q.source)
    (hQ : ∀ a, (e a).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hCQ : S ∩ frontier E ⊆ Q.source)
    (hG : G.faces.Finite) (hGs : G.space = Q '' (S ∩ frontier E))
    (hpres : HasDisjointPolygonPresentation G.space)
    (hGc : ∀ a ∈ G.faces, a.card ≤ 2)
    (hdegree : ∀ v : G.vertices,
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hcross : ∀ w ∈ G.space, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ C : OpenPartialHomeomorph V3 C3,
        w ∈ C.source ∧ C.source ⊆ O ∩ Q.target ∧
        (∀ z ∈ C.source, Q.symm z ∈ interior R) ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        LocallyPiecewiseAffineOn C.symm C.target ∧
        (∀ x ∈ C.source, Q.symm x ∈ S ↔ (C x).2 = 0) ∧
        ∀ x ∈ C.source, Q.symm x ∈ frontier E ↔ (C x).1.1 = 0)
    (hmin : ∀ d : Set X × OpenPartialHomeomorph X V3 × SimplicialComplex ℝ V3,
      (Nonempty (ChartwisePLSphere e d.1) ∧ d.1 ⊆ interior R ∧
        (¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B d.1)) ∧
        D ⊆ d.2.1.source ∧
        (∀ a, (e a).symm.trans d.2.1 ∈ piecewiseAffineGroupoid V3) ∧
        d.1 ∩ frontier E ⊆ d.2.1.source ∧
        d.2.2.faces.Finite ∧ d.2.2.space = d.2.1 '' (d.1 ∩ frontier E) ∧
        HasDisjointPolygonPresentation d.2.2.space ∧
        (∀ a ∈ d.2.2.faces, a.card ≤ 2) ∧
        (∀ v : d.2.2.vertices,
          (d.2.2.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
        ∀ w ∈ d.2.2.space, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ C : OpenPartialHomeomorph V3 C3,
            w ∈ C.source ∧ C.source ⊆ O ∩ d.2.1.target ∧
            (∀ z ∈ C.source, d.2.1.symm z ∈ interior R) ∧ C w = 0 ∧
            LocallyPiecewiseAffineOn C C.source ∧
            LocallyPiecewiseAffineOn C.symm C.target ∧
            (∀ x ∈ C.source, d.2.1.symm x ∈ d.1 ↔ (C x).2 = 0) ∧
            ∀ x ∈ C.source, d.2.1.symm x ∈ frontier E ↔ (C x).1.1 = 0) →
      Nat.card (ConnectedComponents G.space) ≤
        Nat.card (ConnectedComponents d.2.2.space))
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) {B : Set P2} (p : P2 → X)
    (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space) (hps : p '' K.space = S ∩ E)
    (hproperA : ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B)
    {d q : Set V} (hd : IsFinitePLBallPair P2 d q) (j : V → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjE : MapsTo j d (interior E))
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (gamma : C(Rim,↥(S ∩ E)))
    (hrange : range (fun z => (gamma z : X)) ⊆ j '' q) :
    gamma.Nullhomotopic := by
  have hcrossO : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0 := by
    intro x hx
    obtain ⟨C,hxC,_,_,hC0,hC,_,hCS,hCE⟩ :=
      hcross (Q x) (hGs.symm.subset (mem_image_of_mem Q hx)) univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing Q hQ C hC (hCQ hx) hxC hC0 hCS hCE
  have hproperK : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ K.space ∩ B :=
    fun z hz => (hproperA z hz).trans ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hfront := s.planar_exterior_frontier_eq heE K hK inter_subset_left
    p hp hpi hps hproperK hcrossO
  obtain ⟨n,L,hL,hLi,hLA,hcircle⟩ := exists_original_planar_polygon_for_disk_rim
    he.compatible K hK p hp hpi hps hfront hproperA hd j hj hji hjE hproper
  have hfill := s.polygon_disk_of_proper_compression_at_minimum he hR hSR hn hE hER
    Q G hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
    (K.isCompact_space_of_finite hK) p hp.continuousOn hpi hps hproperA
    L hL hLi hLA hd j hj hji hjE hproper hcircle
  exact nullhomotopic_of_original_planar_polygon_filling (K.isCompact_space_of_finite hK)
    p hp.continuousOn hpi hps L hL hLi (fun x hx => interior_subset (hfill hx).1)
    gamma (hrange.trans hcircle.symm.subset)

end PoincareConjecture.M76
