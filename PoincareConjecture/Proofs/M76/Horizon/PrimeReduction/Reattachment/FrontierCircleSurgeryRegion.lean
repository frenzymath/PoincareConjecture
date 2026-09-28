import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FrontierDiskChartModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocorePositionedProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.PairedCrossingChartChange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedFiniteSphereCut

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_disk_contact_neighborhood
    {X : Type*} [TopologicalSpace X] {D L S T U : Set X}
    (hS : IsClosed S) (hDT : D ⊆ T) (hcontact : D ∩ S = L)
    (hLopen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' L))
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ D ⊆ V ∧ V ⊆ U ∧
      ∀ x ∈ V, x ∈ L ↔ x ∈ S ∧ x ∈ T := by
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hLopen
  have hmem (x : X) (hxS : x ∈ S) (hxT : x ∈ T) : x ∈ O ↔ x ∈ L := by
    change (⟨x, hxS, hxT⟩ : (S ∩ T : Set X)) ∈ (Subtype.val ⁻¹' O) ↔ _
    rw [hOeq]
    rfl
  refine ⟨(O ∪ Sᶜ) ∩ U, (hO.union hS.isOpen_compl).inter hU, ?_,
    inter_subset_right, ?_⟩
  · intro x hx
    refine ⟨?_, hDU hx⟩
    by_cases hxS : x ∈ S
    · exact Or.inl ((hmem x hxS (hDT hx)).mpr (hcontact.subset ⟨hx, hxS⟩))
    · exact Or.inr hxS
  · intro x hx
    constructor
    · intro hxL
      have hh := hcontact.symm.subset hxL
      exact ⟨hh.2, hDT hh.1⟩
    · rintro ⟨hxS, hxT⟩
      apply (hmem x hxS hxT).mp
      exact hx.1.resolve_right (fun h => h hxS)

theorem ChartwisePLSphere.exists_frontier_disk_crossing_scene
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {P T S U : Set X}
    (t : ChartwisePLSphere e T) (s : ChartwisePLSphere e S)
    (hP : IsCompact P) (he : PLDomain e P) (hTP : T ⊆ interior P)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hcontact : p '' d ∩ S = p '' r)
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d)
    (hU : IsOpen U) (hpU : p '' d ⊆ U)
    (hrOpen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r)))
    (Q₀ : OpenPartialHomeomorph X V3)
    (hQ₀ : ∀ i, (e i).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3)
    (hrQ₀ : p '' r ⊆ Q₀.source)
    (hcross : ∀ w ∈ Q₀ '' (p '' r), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q₀.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q₀.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q₀.symm x ∈ T ↔ (B x).1.1 = 0) :
    ∃ (Q : OpenPartialHomeomorph X V3) (n : ℕ) (L : Polygon V3 (n + 3))
      (J : SimplicialComplex ℝ V3) (D : Set V3),
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      Q.source ⊆ interior P ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      IsFinitePLBallPair P2 D (L.boundary ℝ) ∧
      D ⊆ interior J.space ∩ {x | (markedProductCoordinates x).2 = 0} ∧
      D ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
      Q.symm '' D = p '' d ∧
      Q.symm '' L.boundary ℝ = p '' r ∧
      Q.symm '' interior J.space ⊆ U ∧
      (∀ x ∈ Q.target, Q.symm x ∈ T ↔ x 2 = 0) ∧
      Q.target = ball (0 : V3) 1 ∧
      (∀ x ∈ interior J.space, x ∈ L.boundary ℝ ↔
        Q.symm x ∈ S ∧ (markedProductCoordinates x).2 = 0) ∧
      ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 C3,
          w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, (markedProductCoordinates x).2 = 0 ↔ (B x).1.1 = 0 := by
  obtain ⟨Q, n, L, hpQ, hQP, hQ, hQT, _, _, hLi, hL, hD, hLr, hDT,
    hDcontact, hbackD, hbackr, hQtarget⟩ :=
    t.exists_flattened_disk_model hP he hTP hd p hp hpi hpT hcontact pole hpoleT hpole
  obtain ⟨V, hV, hpV, hVU, hVcontact⟩ :=
    exists_disk_contact_neighborhood s.isCompact.isClosed hpT hcontact hrOpen hU hpU
  let D := (Q ∘ p) '' d
  let W := Q.target ∩ Q.symm ⁻¹' V
  have hW : IsOpen W := Q.symm.isOpen_inter_preimage hV
  have hDW : D ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Q.map_source (hpQ ⟨x, hx, rfl⟩), ?_⟩
    change Q.symm (Q (p x)) ∈ V
    rw [Q.left_inv (hpQ ⟨x, hx, rfl⟩)]
    exact hpV ⟨x, hx, rfl⟩
  obtain ⟨J, hJ, hDJ, hJW⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hD.isCompact hW hDW
  have hJQ : J.space ⊆ Q.target := fun _ hx => (hJW hx).1
  have hLT : L.boundary ℝ ⊆ Q.target := hD.1.trans (fun _ hx => (hDT hx).1)
  have hLmem (x : V3) (hx : x ∈ Q.target) : x ∈ L.boundary ℝ ↔ Q.symm x ∈ p '' r := by
    rw [← hbackr]
    exact (Q.symm.injOn.mem_image_iff hLT hx).symm
  have hTmem (x : V3) (hx : x ∈ Q.target) : Q.symm x ∈ T ↔ x 2 = 0 := by
    rw [hQT (Q.symm x) (Q.map_target hx), Q.right_inv hx]
  have hisolate (x : V3) (hx : x ∈ interior J.space) :
      x ∈ L.boundary ℝ ↔ Q.symm x ∈ S ∧ (markedProductCoordinates x).2 = 0 := by
    rw [hLmem x (hJQ (interior_subset hx)), hVcontact _ (hJW (interior_subset hx)).2,
      hTmem x (hJQ (interior_subset hx))]
    rfl
  have hcrossQ : ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, (markedProductCoordinates x).2 = 0 ↔ (B x).1.1 = 0 := by
    intro w hw O hO hwO
    have hwQ := hLT hw
    have hwr := (hLmem w hwQ).mp hw
    have hwS := (hcontact.symm.subset hwr).2
    have hwT := hpT (hcontact.symm.subset hwr).1
    have hwQ₀ := hrQ₀ hwr
    obtain ⟨B, hwB, _, hB0, hB, hBi, hBS, hBT⟩ :=
      hcross (Q₀ (Q.symm w)) ⟨Q.symm w, hwr, rfl⟩
        univ isOpen_univ (mem_univ _)
    obtain ⟨C, hwC, hCO, hC0, hC, hCi, hCS, hCT⟩ :=
      paired_crossing_chart_in_compatible_chart Q₀ Q hQ₀ hQ (he.cover _)
        hwQ₀ (Q.map_target hwQ) B hwB hB0 hB hBi hBS hBT
        (hO.inter isOpen_interior)
        (by rw [Q.right_inv hwQ]; exact ⟨hwO, hDJ (hD.1 hw)⟩)
    rw [Q.right_inv hwQ] at hwC hC0
    refine ⟨C, hwC, fun x hx => (hCO hx).1, hC0, hC, hCi, hCS, ?_⟩
    intro x hx
    exact (hTmem x (hCO hx).2).symm.trans (hCT x hx)
  refine ⟨Q, n, L, J, D, hQ, hQP, hJ, hJQ, hLi, hL, hD,
    (fun x hx => ⟨hDJ hx, (hDT hx).2⟩), hDcontact, hbackD, hbackr, ?_,
    hTmem, hQtarget, hisolate, hcrossQ⟩
  rintro x ⟨y, hy, rfl⟩
  exact hVU (hJW (interior_subset hy)).2

theorem ChartwisePLSphere.exists_frontier_disk_surgery_product_of_rim_chart
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {P T S U : Set X}
    (t : ChartwisePLSphere e T) (s : ChartwisePLSphere e S)
    (hP : IsCompact P) (he : PLDomain e P) (hTP : T ⊆ interior P)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hcontact : p '' d ∩ S = p '' r)
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d)
    (hU : IsOpen U) (hpU : p '' d ⊆ U)
    (hrOpen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r)))
    (Q₀ : OpenPartialHomeomorph X V3)
    (hQ₀ : ∀ i, (e i).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3)
    (hrQ₀ : p '' r ⊆ Q₀.source)
    (hcross : ∀ w ∈ Q₀ '' (p '' r), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q₀.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q₀.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q₀.symm x ∈ T ↔ (B x).1.1 = 0) :
    ∃ rho : V2 × ℝ → X,
      PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) U ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, rho z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ c : Bool, Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)})) T) ∧
      (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩ T = p '' r := by
  obtain ⟨Q, n, L, J, D, hQ, hQP, hJ, hJQ, hLi, hL, hD, hDsub,
    hDcontact, hbackD, hbackr, hJU, hTmem, hQtarget, hisolate, hcrossQ⟩ :=
    t.exists_frontier_disk_crossing_scene s hP he hTP hd p hp hpi hpT hcontact
      pole hpoleT hpole hU hpU hrOpen Q₀ hQ₀ hrQ₀ hcross
  obtain ⟨rho, hρ, hρi, hρQ, hρS, hρcaps, hρband⟩ :=
    s.exists_cocore_positioned_product_of_disk_of_paired_charts he.cover Q hQ J hJ hJQ
      markedProductCoordinates 0 L hLi hL hD
      hDsub hDcontact
      isOpen_interior (fun _ hx => (hDsub hx).1) subset_rfl hisolate hcrossQ
  have hρsource : MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) Q.source := by
    intro z hz
    obtain ⟨x, hx, hxeq⟩ := hρQ hz
    exact hxeq ▸ Q.map_target (hJQ (interior_subset hx))
  have hlevel (x : X) (hx : x ∈ Q.source) :
      x ∈ T ↔ x ∈ Q.symm '' (Q.target ∩ {y | (markedProductCoordinates y).2 = 0}) := by
    constructor
    · intro hxT
      refine ⟨Q x, ⟨Q.map_source hx, ?_⟩, Q.left_inv hx⟩
      exact (hTmem (Q x) (Q.map_source hx)).mp (by rwa [Q.left_inv hx])
    · rintro ⟨y, hy, rfl⟩
      exact (hTmem y hy.1).mpr hy.2
  have hcapfull (c : Bool) : Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)} ⊆
      Disk ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzt : z.2 = if c then (1/2 : ℝ) else -(1/2) := hz.2
    rw [hzt]
    cases c <;> norm_num
  have hbandfull : Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2) ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  refine ⟨rho, hρ, hρi, ?_, hρS, ?_, ?_⟩
  · intro z hz
    exact hJU (hρQ hz)
  · intro c
    apply disjoint_left.mpr
    rintro x hx hxT
    exact disjoint_left.mp (hρcaps c) hx ((hlevel x (by
      obtain ⟨z, hz, rfl⟩ := hx
      exact hρsource (hcapfull c hz))).mp hxT)
  · rw [← hbackr, ← hρband]
    ext x
    constructor
    · rintro ⟨hx, hxT⟩
      exact ⟨hx, (hlevel x (by
        obtain ⟨z, hz, rfl⟩ := hx
        exact hρsource (hbandfull hz))).mp hxT⟩
    · rintro ⟨hx, hxT⟩
      exact ⟨hx, (hlevel x (by
        obtain ⟨z, hz, rfl⟩ := hx
        exact hρsource (hbandfull hz))).mpr hxT⟩

theorem ChartwisePLSphere.exists_frontier_disk_surgery_product
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {P T S U : Set X}
    (t : ChartwisePLSphere e T) (s : ChartwisePLSphere e S)
    (hP : IsCompact P) (he : PLDomain e P) (hTP : T ⊆ interior P)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hcontact : p '' d ∩ S = p '' r)
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d)
    (hU : IsOpen U) (hpU : p '' d ⊆ U)
    (hrOpen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r)))
    (Q₀ : OpenPartialHomeomorph X V3)
    (hQ₀ : ∀ i, (e i).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3)
    (hTQ₀ : T ⊆ Q₀.source)
    (hcross : ∀ w ∈ Q₀ '' (p '' r), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q₀.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q₀.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q₀.symm x ∈ T ↔ (B x).1.1 = 0) :
    ∃ rho : V2 × ℝ → X,
      PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) U ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, rho z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ c : Bool, Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)})) T) ∧
      (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩ T = p '' r := by
  exact t.exists_frontier_disk_surgery_product_of_rim_chart s hP he hTP
    hd p hp hpi hpT hcontact pole hpoleT hpole hU hpU hrOpen Q₀ hQ₀
    ((image_mono hd.1).trans (hpT.trans hTQ₀)) hcross

theorem ChartwisePLSphere.exists_original_frontier_disk_surgery_product
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R T S U : Set X}
    (t : ChartwisePLSphere e T) (s : ChartwisePLSphere e S)
    (hR : IsCompact R) (he : PLDomain e R) (hTR : T ⊆ R)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hcontact : p '' d ∩ S = p '' r)
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d)
    (hU : IsOpen U) (hpU : p '' d ⊆ U)
    (hrOpen : IsOpen ((Subtype.val : (S ∩ T : Set X) → X) ⁻¹' (p '' r)))
    (Q₀ : OpenPartialHomeomorph X V3)
    (hQ₀ : ∀ i, (e i).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3)
    (hTQ₀ : T ⊆ Q₀.source)
    (hcross : ∀ w ∈ Q₀ '' (p '' r), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q₀.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q₀.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q₀.symm x ∈ T ↔ (B x).1.1 = 0) :
    ∃ rho : V2 × ℝ → X,
      PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) U ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, rho z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ c : Bool, Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)})) T) ∧
      (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩ T = p '' r := by
  obtain ⟨P, hP, hRP, heP⟩ := he.exists_compact_ambient_neighborhood hR
  exact t.exists_frontier_disk_surgery_product s hP heP (hTR.trans hRP)
    hd p hp hpi hpT hcontact pole hpoleT hpole hU hpU hrOpen Q₀ hQ₀ hTQ₀ hcross

end PoincareConjecture.M76
